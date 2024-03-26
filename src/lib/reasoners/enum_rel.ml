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

let ret a = fun s -> (a, s)

let bind t f =
  fun s1 ->
  let (a, s2) = t s1 in
  f a s2

let run t s = t s

let (let*) = bind

let iter f l s =
  let s =
    List.fold_left
      (fun s x ->
         let (), s = f x s in
         s
      ) s l
  in
  (), s

module type S = sig
  type t
  type dom

  val empty : t
  (*   val pp : t Fmt.t *)

  val add : X.r -> t -> t
  val update : X.r -> dom -> t -> t
  val subst : ex:Ex.t -> X.r -> X.r -> t -> t
  val propagate : ('a -> X.r -> dom -> 'a) -> 'a -> t -> 'a * t

  val get : X.r -> t -> dom
  val fold : (X.r -> dom -> 'a -> 'a) -> t -> 'a -> 'a
end

module type Domain = sig
  type t

  val unknown : X.r -> t
  (*   val pp : t Fmt.t *)
  val cardinal : t -> int
  val intersect : ex:Ex.t -> t -> t -> t
end

module Make (D : Domain) : S with type dom = D.t = struct
  type dom = D.t

  type t = {
    domains : dom MX.t;
    (* Map of class representatives to domains of their domain.
       The explanation justifies that the semantic value has to lie in this
       domain. *)

    changed : SX.t;
    (* Set of changed domains. *)
  }

  (* let pp ppf t =
     Fmt.(iter_bindings ~sep:semi MX.iter
           (box @@ pair ~sep:(any " ->@ ") X.print D.pp)
         |> braces
        )
      ppf t.domains
  *)
  let empty = { domains = MX.empty; changed = SX.empty }

  let get rr t =
    try MX.find rr t.domains
    with Not_found -> D.unknown rr

  let update rr nd t =
    assert (D.cardinal nd > 0);
    let domains = MX.add rr nd t.domains in
    let changed = SX.add rr t.changed in
    { domains; changed }

  let add rr t =
    match MX.find rr t.domains with
    | _ -> t
    | exception Not_found ->
      let nd = D.unknown rr in
      update rr nd t

  let remove rr t =
    let domains = MX.remove rr t.domains in
    let changed = SX.remove rr t.changed in
    { domains ; changed }

  let subst ~ex rr nrr t =
    match MX.find rr t.domains with
    | d ->
      let nnd =
        match MX.find nrr t.domains with
        | nd -> D.intersect ~ex d nd
        | exception Not_found -> d
      in
      let t = remove rr t in
      update nrr nnd t
    | exception Not_found -> t

  let fold f t acc = MX.fold f t.domains acc

  let propagate f acc t =
    let acc =
      SX.fold
        (fun rr acc ->
           let d = get rr t in
           f acc rr d
        ) t.changed acc
    in
    acc, { t with changed = SX.empty }
end

module Domain = struct
  type t = {
    constrs : HSS.t;
    ex : Ex.t;
  }

  exception Inconsistent of Ex.t

  let[@inline always] expl { ex; _ } = ex

  let[@inline always] cardinal { constrs; _ } = HSS.cardinal constrs

  let[@inline always] choose { constrs; _ } = HSS.choose constrs

  let domain ~constrs ex =
    if HSS.is_empty constrs then
      raise_notrace @@ Inconsistent ex
    else
      { constrs; ex }

  let unknown rr =
    match Th.embed rr with
    | Cons (c, _) ->
      domain ~constrs:(HSS.singleton c) Ex.empty
    | _ ->
      match X.type_info rr with
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

  (* let pp ppf d =
     Fmt.pf ppf "%a"
      Fmt.(iter ~sep:comma HSS.iter Hstring.print) d.constrs;
     if Options.(get_verbose () || get_unsat_core ()) then
      Fmt.pf ppf " %a" (Fmt.box Ex.print) d.ex
  *)
  let intersect ~ex d1 d2 =
    let constrs = HSS.inter d1.constrs d2.constrs in
    let ex = ex |> Ex.union d1.ex |> Ex.union d2.ex in
    domain ~constrs ex

  let complement ~ex d1 d2 =
    let constrs =
      HSS.filter (fun c -> not @@ HSS.mem c d2.constrs) d1.constrs
    in
    let ex = ex |> Ex.union d1.ex |> Ex.union d2.ex in
    domain ~constrs ex
end

module Domains = Make (Domain)

type t = {
  domains : Domains.t;
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

let empty classes = {
  domains = Domains.empty;
  classes = classes;
  size_splits = Numbers.Q.one
}

let get_domain r uf env =
  let rr, _ = Uf.find_r uf r in
  (rr, Domains.get rr env.domains), env

let update_domain rr nd env =
  (), { env with domains = Domains.update rr nd env.domains }

let subst ~ex r1 r2 env =
  (), { env with domains = Domains.subst ~ex r1 r2 env.domains }

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

let propagate_eq ~ex r1 r2 uf =
  let* rr1, d1 = get_domain r1 uf in
  let* rr2, d2 = get_domain r2 uf in
  let nd = Domain.intersect ~ex d1 d2 in
  let* () = update_domain rr1 nd in
  update_domain rr2 nd

let propagate_diseq ~ex r1 r2 uf =
  let* rr1, d1 = get_domain r1 uf in
  let* rr2, d2 = get_domain r2 uf in
  let* () =
    if Domain.cardinal d1 = 1 then
      let nd = Domain.complement ~ex d2 d1 in
      update_domain rr2 nd
    else
      ret ()
  in
  if Domain.cardinal d2 = 1 then
    let nd = Domain.complement ~ex d1 d2 in
    update_domain rr1 nd
  else
    ret ()

let is_enum r =
  match X.type_info r with
  | Ty.Tsum _ -> true
  | _ -> false

let propagate_literals la uf =
  iter
    (fun lit ->
       let open Xliteral in
       match lit with
       | Eq (r1, r2), _, ex, origin when is_enum r1 ->
         begin match origin with
           | Th_util.Subst ->
             subst ~ex r1 r2
           | _ ->
             propagate_eq ~ex r1 r2 uf
         end
       | Distinct (false, [r1; r2]), _, ex, _ when is_enum r2 ->
         propagate_diseq ~ex r1 r2 uf
       | _ ->
         ret ()
    ) la

let propagate_domains env =
  Domains.propagate
    (fun eqs rr d ->
       if Domain.cardinal d = 1 then
         let c = Domain.choose d in
         let nr = Th.is_mine (Cons (c, X.type_info rr)) in
         let ex = Domain.expl d in
         let eq = Literal.LSem (LR.mkv_eq rr nr), ex, Th_util.Other in
         eq :: eqs
       else
         eqs
    ) [] env.domains

let assume env uf la =
  let env = count_splits env la in
  let classes = Uf.cl_extract uf in
  let env = { env with classes = classes } in
  let (), env =
    try
      run (propagate_literals la uf) env
    with Domain.Inconsistent ex ->
      raise_notrace (Ex.Inconsistent (ex, env.classes))
  in
  let assume, domains = propagate_domains env in
  { env with domains }, Sig_rel.{ assume; remove = [] }

let add env uf r _t =
  match X.type_info r with
  | Ty.Tsum _ ->
    let rr, _ = Uf.find_r uf r in
    { env with domains = Domains.add rr env.domains }, []
  | _ ->
    env, []

let cs_criteria env n =
  let m = Options.get_max_split () in
  Numbers.Q.(compare (mult n env.size_splits) m) <= 0 || Numbers.Q.sign m < 0

(* Do a case-split by choosing a value for class representatives having of
   minimal size. *)
let case_split env _uf ~for_model =
  let best =
    Domains.fold (fun r d best ->
        let cd = Domain.cardinal d in
        if cd > 1 then
          match best with
          | Some (n, _, _) when n <= cd -> best
          | _ -> Some (cd, r, Domain.choose d)
        else
          best
      ) env.domains None
  in
  match best with
  | Some (n, r, c) ->
    let n = Numbers.Q.from_int n in
    if for_model || cs_criteria env n then
      let nr = Th.is_mine (Cons (c, X.type_info r)) in
      [LR.mkv_eq r nr, true, Th_util.CS (Th_util.Th_sum, n)]
    else
      []
  | None ->
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
