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

module Function = struct
  type t = {
    e : Expr.t;
    is_max : bool;
  }

  let equal { e = e1; is_max = m1 } { e = e2; is_max = m2 } =
    Bool.equal m1 m2 && Expr.equal e1 e2

  let mk ~is_max e = { e; is_max }

  let pp ppf { e; _ } = Expr.print ppf e
end

module Value = struct
  type limit_kind =
    | Above
    | Below

  type t =
    | Minfinity
    | Pinfinity
    | Value of Expr.t
    | Limit of limit_kind * Expr.t
    | Unknown

  let pp ppf v =
    match v with
    | Minfinity -> Fmt.pf ppf "-oo"
    | Pinfinity -> Fmt.pf ppf "+oo"
    | Value w -> Expr.print ppf w
    | Limit (Above, w) -> Fmt.pf ppf "(+ %a epsilon)" Expr.print w
    | Limit (Below, w) -> Fmt.pf ppf "(- %a epsilon)" Expr.print w
    | Unknown -> Fmt.pf ppf "(interval (- oo) (+ oo))"
end

module Model = struct
  type s = { f: Function.t; order: int }

  module M =  Map.Make (struct
      type t = s

      let compare { order = o1; _ } { order = o2; _ } = o1 - o2
    end)

  type t = Value.t M.t

  let empty = M.empty
  let is_empty = M.is_empty
  let fold g = M.fold (fun { f; _ } acc -> g f acc)

  let add o v mdl =
    let order =
      match M.find_first (fun { f; _ } -> Function.equal f o) mdl with
      | ({ order; _ }, _) -> order
      | exception Not_found -> M.cardinal mdl
    in
    M.add { f = o; order } v mdl

  let pp_binding ppf ({ f; _ }, v) =
    Fmt.pf ppf "(%a %a)" Function.pp f Value.pp v

  let pp ppf mdl =
    if M.is_empty mdl then
      Fmt.pf ppf "@[<v 2>(objectives @]@,)"
    else
      Fmt.pf ppf "@[<v 2>(objectives @,%a@]@,)"
        (Fmt.iter_bindings ~sep:Fmt.cut M.iter pp_binding) mdl

  let functions mdl =
    M.bindings mdl
    |> List.map (fun ({ f; _ }, _) -> f)

  let has_no_limit mdl =
    M.for_all
      (fun _ v ->
         match (v : Value.t) with
         | Pinfinity | Minfinity | Limit _ -> false
         | Value _ | Unknown -> true
      ) mdl

  let reset_until mdl o =
    M.fold
      (fun { f; order } v acc ->
         if order < o then M.add { f; order } v acc
         else M.add { f; order } Value.Unknown acc
      )
      mdl M.empty
end
