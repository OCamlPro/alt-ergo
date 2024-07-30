(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2022-2024 --- OCamlPro SAS                           *)
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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module Function = struct
  type index = int

  type t = {
    e : Expr.t;
    is_max : bool;
    index : index;
  }

  let cnt = ref 0

  let compare { index = i1; _ } { index = i2; _ } = i1 - i2

  let mk ~is_max e =
    let r = { e; is_max; index = !cnt } in
    incr cnt;
    r

  let pp ppf { e; _ } = Expr.print ppf e

  let reinit_cnt () = cnt := 0
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
    | Minfinity -> Fmt.pf ppf "(- oo)"
    | Pinfinity -> Fmt.pf ppf "(+ oo)"
    | Value w -> Expr.print ppf w
    | Limit (Above, w) -> Fmt.pf ppf "(+ %a epsilon)" Expr.print w
    | Limit (Below, w) -> Fmt.pf ppf "(- %a epsilon)" Expr.print w
    | Unknown -> Fmt.pf ppf "(interval (- oo) (+ oo))"
end

module Model = struct
  module M =  Map.Make (Function)

  type t = Value.t M.t

  let empty = M.empty
  let is_empty = M.is_empty
  let fold = M.fold
  let add = M.add

  let pp_binding ppf (fn, v) =
    Fmt.pf ppf "(%a %a)" Function.pp fn Value.pp v

  let pp ppf mdl =
    if M.is_empty mdl then
      Fmt.pf ppf "@[<v 2>(objectives @]@,)"
    else
      Fmt.pf ppf "@[<v 2>(objectives @,%a@]@,)"
        (Fmt.iter_bindings ~sep:Fmt.cut M.iter pp_binding) mdl

  let functions mdl =
    M.bindings mdl
    |> List.map (fun (fn, _) -> fn)

  let has_no_limit mdl =
    M.for_all
      (fun _ v ->
         match (v : Value.t) with
         | Pinfinity | Minfinity | Limit _ -> false
         | Value _ | Unknown -> true
      ) mdl

  exception Found of Function.t

  let next_unknown mdl =
    try
      M.iter (fun fn v ->
          match (v : Value.t) with
          | Unknown -> raise (Found fn)
          | Value _ | Limit _ | Pinfinity | Minfinity -> ()
        ) mdl;
      None
    with
    | Found fn -> Some fn
    | Exit -> None
end
