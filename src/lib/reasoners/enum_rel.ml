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

let timer = Timers.M_Sum

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

  let pp ppf t =
    Fmt.(iter_bindings ~sep:semi MX.iter
           (box @@ pair ~sep:(any " ->@ ") X.print Domain.pp)
         |> braces
        )
      ppf t.domains

  let empty = { domains = MX.empty; changed = SX.empty }

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
    if MX.mem r t.domains then t
    else
      match Th.embed r with
      | Cons _ -> t
      | _ ->
        (* We have to add a default domain if the key `r` isn't in map in order
           to be sure that the case-split mechanism will attempt to choose a
           value for it. *)
        let nd = Domain.unknown (X.type_info r) in
        internal_update r nd t

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

    | exception Not_found -> t

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
  domains : Domains.t;
  (* Map of class representatives of enum semantic values to their
     domains. *)

  classes : Expr.Set.t list;
  (* State of the union-find represented by all its equivalence classes.
     This state is kept for debugging purposes only. It is updated with
     [Uf.cl_extract] after assuming literals of the theory and returned by
     queries in case of inconsistency. *)

  size_splits : Numbers.Q.t
  (* Estimate the number of case-splits performed by the theory. The
     estimation is updated while assuming new literals of the theory.
     We don't perfom new case-splits if this estimation exceeds
     [Options.get_max_split ()]. *)
}

(*BISECT-IGNORE-BEGIN*)
module Debug = struct
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

  let pp_env env =
    if Options.get_debug_sum () then
      Printer.print_dbg ~module_name:"Enum_rel"
        "The environment before assuming:@ @[%a@]" Domains.pp env.domains
end
(*BISECT-IGNORE-END*)

let empty classes = {
  domains = Domains.empty;
  classes = classes;
  size_splits = Numbers.Q.one
}

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
  {env with size_splits = nb}

let tighten_domain rr nd env =
  { env with domains = Domains.tighten rr nd env.domains }

(* Update the domains of the semantic values [r1] and [r2] according to
   the substitution `r1 |-> r2`.

   @raise Domain.Inconsistent if this substitution is inconsistent with
          the current environment [env]. *)
let assume_subst ~ex r1 r2 env =
  { env with domains = Domains.subst ~ex r1 r2 env.domains }

(* Update the domains of the semantic values [r1] and [r2] according to the
   disequality [r1 <> r2].

   This function alone isn't sufficient to produce a complete decision
   procedure for the Enum theory. For instance, let's assume we have three
   semantic values [r1], [r2] and [r3] whose the domain is `{C1, C2}`. It's
   clear that `(distinct r1 r2 r3)` is unsatisfiable but we haven't enough
   information to discover this contradiction.

   Now, if we produce a case-split for one of these semantic values,
   we reach a contradiction for each choice and so our implementation got
   a complete decision procedure (assuming we have fuel to produce enough
   case-splits).

   @raise Domain.Inconsistent if the disequality is inconsistent with
          the current environment [env]. *)
let assume_distinct ~ex r1 r2 env =
  let d1 = Domains.get r1 env.domains in
  let d2 = Domains.get r2 env.domains in
  let env =
    match Domain.as_singleton d1 with
    | Some (c, ex1) ->
      let ex = Ex.union ex1 ex in
      let nd = Domain.remove ~ex c d2 in
      tighten_domain r2 nd env
    | None ->
      env
  in
  match Domain.as_singleton d2 with
  | Some (c, ex2) ->
    let ex = Ex.union ex2 ex in
    let nd = Domain.remove ~ex c d1 in
    tighten_domain r1 nd env
  | None ->
    env

let is_enum r =
  match X.type_info r with
  | Ty.Tsum _ -> true
  | _ -> false

let add r uf env =
  match X.type_info r with
  | Ty.Tsum _ ->
    Debug.add r;
    let rr, _ = Uf.find_r uf r in
    { env with domains = Domains.add rr env.domains }
  | _ ->
    env

let add_rec r uf env =
  List.fold_left (fun env leaf -> add leaf uf env) env (X.leaves r)

let add env uf r _t = add r uf env, []

let assume_literals la uf env =
  List.fold_left
    (fun env lit ->
       let open Xliteral in
       match lit with
       | Eq (r1, r2) as l, _, ex, Th_util.Subst when is_enum r1 ->
         Debug.assume l;
         (* Needed for models generation because fresh terms are not added with
            the function add. *)
         let env = add_rec r1 uf env in
         let env = add_rec r2 uf env in
         assume_subst ~ex r1 r2 env

       | Distinct (false, [r1; r2]) as l, _, ex, _ when is_enum r2 ->
         Debug.assume l;
         (* Needed for models generation because fresh terms are not added with
            the function add. *)
         let env = add_rec r1 uf env in
         let env = add_rec r2 uf env in
         assume_distinct ~ex r1 r2 env

       | _ ->
         (* We ignore [Eq] literals that aren't substitutions as the propagation
            of such equalities will produce substitutions later.
            More precisely, the equation [Eq (r1, r2)] will produce two
            substitutions:
              [Eq (r1, rr)] and [Eq (r2, rr)]
            where [rr] is the new class representative. *)
         env
    ) env la

let propagate_domains env =
  Domains.propagate
    (fun eqs rr d ->
       match Domain.as_singleton d with
       | Some (c, ex) ->
         let nr = Th.is_mine (Cons (c, X.type_info rr)) in
         let eq = Literal.LSem (LR.mkv_eq rr nr), ex, Th_util.Other in
         eq :: eqs
       | None ->
         eqs
    ) [] env.domains

let assume env uf la =
  Debug.pp_env env;
  let env = count_splits env la in
  let classes = Uf.cl_extract uf in
  let env = { env with classes = classes } in
  let env =
    try
      assume_literals la uf env
    with Domain.Inconsistent ex ->
      raise_notrace (Ex.Inconsistent (ex, env.classes))
  in
  let assume, domains = propagate_domains env in
  { env with domains }, Sig_rel.{ assume; remove = [] }

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
      ) env.domains None
  in
  match best with
  | Some (n, r, c) ->
    let n = Numbers.Q.from_int n in
    if for_model || can_split env n then
      let nr = Th.is_mine (Cons (c, X.type_info r)) in
      Debug.case_split r nr;
      [LR.mkv_eq r nr, true, Th_util.CS (Th_util.Th_sum, n)]
    else
      []
  | None ->
    Debug.no_case_split ();
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
