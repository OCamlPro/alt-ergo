(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2024 --- OCamlPro SAS                           *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module L  = List
module X = Shostak.Combine
module Ex = Explanation
module MX = Shostak.MXH
module SX = Shostak.SXH
module LR = Uf.LX
module Th = Shostak.Enum

let timer = Self.M_Sum

module Domain = struct
  type t = {
    constrs : Uid.Set.t;
    ex : Ex.t;
  }

  exception Inconsistent of Ex.t

  let[@inline always] cardinal { constrs; _ } = Uid.Set.cardinal constrs

  let[@inline always] choose { constrs; _ } = Uid.Set.choose constrs

  let[@inline always] as_singleton { constrs; ex } =
    if Uid.Set.cardinal constrs = 1 then
      Some (Uid.Set.choose constrs, ex)
    else
      None

  let domain ~constrs ex =
    if Uid.Set.is_empty constrs then
      raise_notrace @@ Inconsistent ex
    else
      { constrs; ex }

  let[@inline always] singleton ~ex c = { constrs = Uid.Set.singleton c; ex }

  let[@inline always] subset d1 d2 = Uid.Set.subset d1.constrs d2.constrs

  let unknown ty =
    match ty with
    | Ty.Tsum (_, constrs) ->
      (* Return the list of all the constructors of the type of [r]. *)
      let constrs = Uid.Set.of_list constrs in
      assert (not @@ Uid.Set.is_empty constrs);
      { constrs; ex = Ex.empty }
    | _ ->
      (* Only Enum values can have a domain. This case shouldn't happen since
         we check the type of semantic values in both [add] and [assume]. *)
      assert false

  let equal d1 d2 = Uid.Set.equal d1.constrs d2.constrs

  let pp ppf d =
    Fmt.(braces @@
         iter ~sep:comma Uid.Set.iter Uid.pp) ppf d.constrs;
    if Options.(get_verbose () || get_unsat_core ()) then
      Fmt.pf ppf " %a" (Fmt.box Ex.print) d.ex

  let intersect ~ex d1 d2 =
    let constrs = Uid.Set.inter d1.constrs d2.constrs in
    let ex = ex |> Ex.union d1.ex |> Ex.union d2.ex in
    domain ~constrs ex

  let remove ~ex c d =
    let constrs = Uid.Set.remove c d.constrs in
    let ex = Ex.union ex d.ex in
    domain ~constrs ex
end

let is_enum_ty = function
  | Ty.Tsum _ -> true
  | _ -> false

let is_enum r = is_enum_ty (X.type_info r)

module Domains = struct
  (** The type of simple domain maps. A domain map maps each representative
      (semantic value, of type [X.r]) to its associated domain. *)
  type t = {
    domains : Domain.t MX.t;
    (** Map from tracked representatives to their domain.

        We don't store domains for constructors. *)

    changed : SX.t;
    (** Representatives whose domain has changed since the last flush
        in [propagation]. *)
  }

  type _ Uf.id += Id : t Uf.id

  let pp ppf t =
    Fmt.(iter_bindings ~sep:semi MX.iter
           (box @@ pair ~sep:(any " ->@ ") X.print Domain.pp)
         |> braces
        )
      ppf t.domains

  let empty = { domains = MX.empty; changed = SX.empty }

  let filter_ty = is_enum_ty

  let internal_update r nd t =
    let domains = MX.add r nd t.domains in
    let changed = SX.add r t.changed in
    { domains; changed }

  let get r t =
    match Th.embed r with
    | Cons (c, _) ->
      (* For sake of efficiency, we don't look in the map if the
         semantic value is a constructor. *)
      Domain.singleton ~ex:Explanation.empty c
    | _ ->
      try MX.find r t.domains
      with Not_found ->
        Domain.unknown (X.type_info r)

  let add r t =
    match Th.embed r with
    | Alien _ when not (MX.mem r t.domains) ->
      (* We have to add a default domain if the key `r` isn't in map in order
         to be sure that the case-split mechanism will attempt to choose a
         value for it. *)
      let nd = Domain.unknown (X.type_info r) in
      internal_update r nd t
    | Cons _ | Alien _ -> t

  (** [tighten r d t] replaces the domain of [r] in [t] by a domain [d] contains
      in the current domain of [r]. The representative [r] is marked [changed]
      after this call if the domain [d] is strictly smaller. *)
  let tighten r d t =
    let od = get r t in
    (* For sake of completeness, the domain [d] has to be a subset of the old
       domain of [r]. *)
    Options.heavy_assert (fun () -> Domain.subset d od);
    if Domain.equal od d then
      t
    else
      internal_update r d t

  let remove r t =
    let domains = MX.remove r t.domains in
    let changed = SX.remove r t.changed in
    { domains ; changed }

  exception Inconsistent = Domain.Inconsistent

  (** [subst ~ex p v d] replaces all the instances of [p] with [v] in all
      domains, merging the corresponding domains as appropriate.

      The explanation [ex] justifies the equality [p = v].

      @raise Domain.Inconsistent if this causes any domain in [d] to become
             empty. *)
  let subst ~ex r nr t =
    match MX.find r t.domains with
    | d ->
      let nd = Domain.intersect ~ex d (get nr t) in
      let t = remove r t in
      tighten nr nd t

    | exception Not_found -> add nr t

  let fold f t acc = MX.fold f t.domains acc

  (* [propagate f a t] iterates on all the changed domains of [t] since the
     last call of [propagate]. The list of changed domains is flushed after
     this call. *)
  let propagate f acc t =
    let acc =
      SX.fold
        (fun r acc ->
           let d = get r t in
           f acc r d
        ) t.changed acc
    in
    acc, { t with changed = SX.empty }
end

type t = {
  size_splits : Numbers.Q.t
  (* Estimate the number of case-splits performed by the theory. The
     estimation is updated while assuming new literals of the theory.
     We don't perfom new case-splits if this estimation exceeds
     [Options.get_max_split ()]. *)
}

<<<<<<< HEAD
||||||| parent of 0448389c1 (Use logs for debug printing)
let empty classes = {
  mx = MX.empty;
  classes = classes;
  size_splits = Numbers.Q.one
}

=======
let empty classes = {
  mx = MX.empty;
  classes = classes;
  size_splits = Numbers.Q.one
}

module P = Printer.Make (struct let mod_ = Self.M_Sum end)

>>>>>>> 0448389c1 (Use logs for debug printing)
(*BISECT-IGNORE-BEGIN*)
module Debug = struct
<<<<<<< HEAD
  let assume l =
    if Options.get_debug_sum () then
      Printer.print_dbg ~module_name:"Enum_rel" ~function_name:"assume"
        "assume %a"
        (Xliteral.print_view X.print) l

  let case_split r1 r2 =
    if Options.get_debug_sum () then
      Printer.print_dbg ~module_name:"Enum_rel" ~function_name:"case_split"
        "%a = %a" X.print r1 X.print r2

  let no_case_split () =
    if Options.get_debug_sum () then
      Printer.print_dbg ~module_name:"Enum_rel" ~function_name:"case_split"
        "nothing"

  let add r =
    if Options.get_debug_sum () then
      Printer.print_dbg ~module_name:"Enum_rel" ~function_name:"add"
        "%a" X.print r

  let pp_domains domains =
    if Options.get_debug_sum () then
      Printer.print_dbg ~module_name:"Enum_rel"
        "The environment before assuming:@ @[%a@]" Domains.pp domains
||||||| parent of 0448389c1 (Use logs for debug printing)
  open Printer

  let assume bol r1 r2 =
    if Options.get_debug_sum () then
      print_dbg
        ~module_name:"Enum_rel" ~function_name:"assume"
        "we assume %a %s %a"
        X.print r1 (if bol then "=" else "<>") X.print r2

  let print_env env =
    if Options.get_debug_sum () then begin
      Printer.print_dbg ~flushed:false
        ~module_name:"Enum_rel" ~function_name:"print_env"
        "@[<v 2>--SUM env ---------------------------------@ ";
      MX.iter
        (fun r (hss, ex) ->
           Printer.print_dbg  ~flushed:false ~header:false
             "%a ::= " X.print r;
           begin
             match HSS.elements hss with
               []      -> ()
             | hs :: l ->
               Printer.print_dbg  ~flushed:false ~header:false
                 " %s" (Hs.view hs);
               L.iter (fun hs ->
                   Printer.print_dbg  ~flushed:false ~header:false
                     " | %s" (Hs.view hs)) l
           end;
           Printer.print_dbg ~flushed:false ~header:false
             " : %a@ " Ex.print ex;
        ) env.mx;
      Printer.print_dbg ~header:false
        "@ -------------------------------------------";
    end

  let case_split r r' =
    if Options.get_debug_sum () then
      Printer.print_dbg
        ~module_name:"Enum_rel" ~function_name:"case_split"
        "%a = %a" X.print r X.print r'

  let no_case_split () =
    if Options.get_debug_sum () then
      Printer.print_dbg
        ~module_name:"Enum_rel" ~function_name:"no_case_split"
        "sum: nothing"

  let add r =
    if Options.get_debug_sum () then
      Printer.print_dbg
        ~module_name:"Enum_rel" ~function_name:"add"
        "%a" X.print r

=======
  let print_env env =
    if Options.get_debug_sum () then begin
      Printer.print_dbg ~flushed:false
        ~module_name:"Enum_rel" ~function_name:"print_env"
        "@[<v 2>--SUM env ---------------------------------@ ";
      MX.iter
        (fun r (hss, ex) ->
           Printer.print_dbg  ~flushed:false ~header:false
             "%a ::= " X.print r;
           begin
             match HSS.elements hss with
               []      -> ()
             | hs :: l ->
               Printer.print_dbg  ~flushed:false ~header:false
                 " %s" (Hs.view hs);
               L.iter (fun hs ->
                   Printer.print_dbg  ~flushed:false ~header:false
                     " | %s" (Hs.view hs)) l
           end;
           Printer.print_dbg ~flushed:false ~header:false
             " : %a@ " Ex.print ex;
        ) env.mx;
      Printer.print_dbg ~header:false
        "@ -------------------------------------------";
    end
>>>>>>> 0448389c1 (Use logs for debug printing)
end
(*BISECT-IGNORE-END*)

let empty uf = {
  size_splits = Numbers.Q.one
}, Uf.GlobalDomains.add (module Domains) Domains.empty (Uf.domains uf)

(* Update the counter of case-split size in [env]. *)
let count_splits env la =
  let nb =
    List.fold_left
      (fun nb (_, _, _, i) ->
         match i with
         | Th_util.CS (Th_util.Th_sum, n) -> Numbers.Q.mult nb n
         | _ -> nb
      ) env.size_splits la
  in
  {size_splits = nb}

<<<<<<< HEAD
let tighten_domain rr nd domains =
  Domains.tighten rr nd domains
||||||| parent of 0448389c1 (Use logs for debug printing)
(* Add the uninterpreted semantic value [r] to the environment [env] with
   all the constructors of its type as domain. *)
let add_aux env r =
  Debug.add r;
  match Sh.embed r, values_of r with
  | Alien r, Some hss ->
    if MX.mem r env.mx then env else
      { env with mx = MX.add r (hss, Ex.empty) env.mx }
  | _ -> env
=======
(* Add the uninterpreted semantic value [r] to the environment [env] with
   all the constructors of its type as domain. *)
let add_aux env r =
  P.debug ~fn:Self.F_add (fun k -> k"add %a" X.print r);
  match Sh.embed r, values_of r with
  | Alien r, Some hss ->
    if MX.mem r env.mx then env else
      { env with mx = MX.add r (hss, Ex.empty) env.mx }
  | _ -> env
>>>>>>> 0448389c1 (Use logs for debug printing)

(* Update the domains of the semantic values [r1] and [r2] according to the
   disequality [r1 <> r2].

   This function alone isn't sufficient to produce a complete decision
   procedure for the Enum theory. For instance, let's assume we have three
   semantic values [r1], [r2] and [r3] whose the domain is `{C1, C2}`. It's
   clear that `(distinct r1 r2 r3)` is unsatisfiable but we have not enough
   information to discover this contradiction.

   Now, if we produce a case-split for one of these semantic values,
   we reach a contradiction for each choice and so our implementation got
   a complete decision procedure (assuming we have fuel to produce enough
   case-splits).

   @raise Domain.Inconsistent if the disequality is inconsistent with
          the current environment [env]. *)
let assume_distinct ~ex r1 r2 domains =
  let d1 = Domains.get r1 domains in
  let d2 = Domains.get r2 domains in
  let env =
    match Domain.as_singleton d1 with
    | Some (c, ex1) ->
      let ex = Ex.union ex1 ex in
      let nd = Domain.remove ~ex c d2 in
      tighten_domain r2 nd domains
    | None ->
      domains
  in
  match Domain.as_singleton d2 with
  | Some (c, ex2) ->
    let ex = Ex.union ex2 ex in
    let nd = Domain.remove ~ex c d1 in
    tighten_domain r1 nd env
  | None ->
    env

let add r uf domains =
  match X.type_info r with
  | Ty.Tsum _ ->
    Debug.add r;
    let rr, _ = Uf.find_r uf r in
    Domains.add rr domains
  | _ ->
    domains

let add_rec r uf domains =
  List.fold_left (fun env leaf -> add leaf uf env) domains (X.leaves r)

let add env uf _r _t =
  env, Uf.domains uf, []

let assume_literals la uf domains =
  List.fold_left
    (fun domains lit ->
       let open Xliteral in
       match lit with
       | Distinct (false, [r1; r2]) as l, _, ex, _ when is_enum r2 ->
         Debug.assume l;
         (* Needed for models generation because fresh terms are not added with
            the function add. *)
         let domains = add_rec r1 uf domains in
         let domains = add_rec r2 uf domains in
         assume_distinct ~ex r1 r2 domains

       | _ -> domains
    ) domains la

let propagate_domains domains =
  Domains.propagate
    (fun eqs rr d ->
       match Domain.as_singleton d with
       | Some (c, ex) ->
         let nr = Th.is_mine (Cons (c, X.type_info rr)) in
         let eq = Literal.LSem (LR.mkv_eq rr nr), ex, Th_util.Other in
         eq :: eqs
       | None ->
         eqs
    ) [] domains

let assume env uf la =
  let ds = Uf.domains uf in
  let domains = Uf.GlobalDomains.find (module Domains) ds in
  Debug.pp_domains domains;
  let env = count_splits env la in
<<<<<<< HEAD
  let domains =
    try
      assume_literals la uf domains
    with Domain.Inconsistent ex ->
      raise_notrace (Ex.Inconsistent (ex, Uf.cl_extract uf))
||||||| parent of 0448389c1 (Use logs for debug printing)
  let classes = Uf.cl_extract uf in
  let env = { env with classes = classes } in
  let aux bol r1 r2 dep env eqs = function
    | None     -> env, eqs
    | Some hss ->
      Debug.assume bol r1 r2;
      if bol then
        add_eq hss (Sh.embed r1) (Sh.embed r2) dep env eqs
      else
        add_diseq hss (Sh.embed r1) (Sh.embed r2) dep env eqs
=======
  let classes = Uf.cl_extract uf in
  let env = { env with classes = classes } in
  let aux bol r1 r2 dep env eqs = function
    | None     -> env, eqs
    | Some hss ->
      P.debug ~fn:Self.F_assume
        (fun k -> k"assume@ %a %s %a"
            X.print r1 (if bol then "=" else "<>") X.print r2
        );
      if bol then
        add_eq hss (Sh.embed r1) (Sh.embed r2) dep env eqs
      else
        add_diseq hss (Sh.embed r1) (Sh.embed r2) dep env eqs
>>>>>>> 0448389c1 (Use logs for debug printing)
  in
  let assume, domains = propagate_domains domains in
  env,
  Uf.GlobalDomains.add (module Domains) domains ds,
  Sig_rel.{ assume; remove = [] }

let can_split env n =
  let m = Options.get_max_split () in
  Numbers.Q.(compare (mult n env.size_splits) m) <= 0 || Numbers.Q.sign m < 0

(* Do a case-split by choosing a constructor for class representatives of
   minimal size. *)
let case_split env uf ~for_model =
  let best =
    Domains.fold (fun r d best ->
        let rr, _ = Uf.find_r uf r in
        match Th.embed rr with
        | Cons _ ->
          (* The equivalence class of [r] already contains a model term so
             we don't need to make another case-split for this semantic
             value. *)
          best
        | _ ->
          let cd = Domain.cardinal d in
          match best with
          | Some (n, _, _) when n <= cd -> best
          | _ -> Some (cd, r, Domain.choose d)
      ) (Uf.GlobalDomains.find (module Domains) (Uf.domains uf)) None
  in
  match best with
  | Some (n, r, c) ->
    let n = Numbers.Q.from_int n in
<<<<<<< HEAD
    if for_model || can_split env n then
      let nr = Th.is_mine (Cons (c, X.type_info r)) in
      Debug.case_split r nr;
      [LR.mkv_eq r nr, true, Th_util.CS (Th_util.Th_sum, n)]
||||||| parent of 0448389c1 (Use logs for debug printing)
    if for_model ||
       Numbers.Q.compare
         (Numbers.Q.mult n env.size_splits) (Options.get_max_split ()) <= 0  ||
       Numbers.Q.sign  (Options.get_max_split ()) < 0 then
      let r' = Sh.is_mine (Cons(hs,X.type_info r)) in
      Debug.case_split r r';
      [LR.mkv_eq r r', true, Th_util.CS (Th_util.Th_sum, n)]
=======
    if for_model ||
       Numbers.Q.compare
         (Numbers.Q.mult n env.size_splits) (Options.get_max_split ()) <= 0  ||
       Numbers.Q.sign  (Options.get_max_split ()) < 0 then
      let r' = Sh.is_mine (Cons(hs,X.type_info r)) in
      P.debug ~fn:Self.F_case_split
        (fun k -> k"case split:@ %a = %a" X.print r X.print r');
      [LR.mkv_eq r r', true, Th_util.CS (Th_util.Th_sum, n)]
>>>>>>> 0448389c1 (Use logs for debug printing)
    else
      []
  | None ->
    P.debug ~fn:Self.F_case_split (fun k -> k"no case split found");
    []

let optimizing_objective _env _uf _o = None

let query env uf a_ex =
  try ignore(assume env uf [a_ex]); None
  with Ex.Inconsistent (expl, classes) -> Some (expl, classes)

let new_terms _ = Expr.Set.empty

let instantiate ~do_syntactic_matching:_ _ env _ _  = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Sum ->
    failwith "This Theory does not support theories extension"
  | _ -> t
