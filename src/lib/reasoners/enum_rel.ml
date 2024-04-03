(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
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
module HSS = Set.Make (Hstring)
module LR = Uf.LX
module Th = Shostak.Enum

let timer = Timers.M_Sum

module Domain = struct
  type t = {
    constrs : HSS.t;
    ex : Ex.t;
  }

  exception Inconsistent of Ex.t

  let[@inline always] cardinal { constrs; _ } = HSS.cardinal constrs

  let[@inline always] choose { constrs; _ } = HSS.choose constrs

  let[@inline always] as_singleton { constrs; _ } =
    if HSS.cardinal constrs = 1 then
      Some (HSS.choose constrs)
    else
      None

  let domain ~constrs ex =
    if HSS.is_empty constrs then
      raise_notrace @@ Inconsistent ex
    else
      { constrs; ex }

  let unknown r =
    match Th.embed r with
    | Cons (c, _) ->
      domain ~constrs:(HSS.singleton c) Ex.empty
    | _ ->
      match X.type_info r with
      | Ty.Tsum (_, constrs) ->
        (* Return the list of all the constructors of the type of [r]. *)
        let constrs = HSS.of_list constrs in
        assert (not @@ HSS.is_empty constrs);
        { constrs; ex = Ex.empty }
      | _ ->
        (* Only Enum values can have a domain. This case can happen since we
           don't dispatch the literals processed in [assume] by their types in
           the Relation module. *)
        invalid_arg "unknown"

  let equal d1 d2 = HSS.equal d1.constrs d2.constrs

  let pp ppf d =
    Fmt.pf ppf "%a"
      Fmt.(iter ~sep:comma HSS.iter Hstring.print) d.constrs;
    if Options.(get_verbose () || get_unsat_core ()) then
      Fmt.pf ppf " %a" (Fmt.box Ex.print) d.ex

  let intersect ~ex d1 d2 =
    let constrs = HSS.inter d1.constrs d2.constrs in
    let ex = ex |> Ex.union d1.ex |> Ex.union d2.ex in
    domain ~constrs ex

  let remove ~ex c d =
    let constrs = HSS.remove c d.constrs in
    let ex = Ex.union ex d.ex in
    domain ~constrs ex
end

module Domains = struct
  exception Inconsistent = Domain.Inconsistent
  (** Exception raised by [update] or [subst] when an inconsistency is
      detected. *)

  (** The type of simple domain maps. A domain map maps each representative
      (semantic value, of type [X.r]) to its associated domain. *)
  type t = {
    domains : Domain.t MX.t;
    (** Map from tracked representatives to their domain. *)

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

  (** [add r t] adds a domain for [r] in the domain map. If [r] does not
      already have an associated domain, a fresh domain will be created for
      [r] using [Domain.unknown]. *)
  let add r t =
    match MX.find r t.domains with
    | _ -> t
    | exception Not_found ->
      let nd = Domain.unknown r in
      internal_update r nd t

  (** [update r d t] replaces the domain of [r] in [t] by [d]. The
      representative [r] is marked [changed] after this call. *)
  let update r d t =
    match MX.find r t.domains with
    | od ->
      let nd = Domain.intersect ~ex:Explanation.empty od d in
      if Domain.equal od nd then
        t
      else
        internal_update r nd t

    | exception Not_found ->
      let nd = Domain.intersect ~ex:Explanation.empty (Domain.unknown r) d in
      internal_update r nd t

  (** [get r t] returns the domain currently associated with [r] in [t]. *)
  let get r t =
    try MX.find r t.domains
    with Not_found -> Domain.unknown r

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
      let nnd =
        match MX.find nr t.domains with
        | nd -> Domain.intersect ~ex d nd
        | exception Not_found -> d
      in
      let t = remove r t in
      internal_update nr nnd t

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

let update_domain rr nd env =
  { env with domains = Domains.update rr nd env.domains }

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
    | Some c ->
      let nd = Domain.remove ~ex c d2 in
      update_domain r2 nd env
    | None ->
      env
  in
  match Domain.as_singleton d2 with
  | Some c ->
    let nd = Domain.remove ~ex c d1 in
    update_domain r1 nd env
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
       | Some c ->
         let nr = Th.is_mine (Cons (c, X.type_info rr)) in
         let eq = Literal.LSem (LR.mkv_eq rr nr), d.ex, Th_util.Other in
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
