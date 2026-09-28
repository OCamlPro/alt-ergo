(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
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

module Path = Dolmen.Std.Path
module DE = Dolmen.Std.Expr

let path_name (p : Path.t) : string =
  match p with
  | Path.Absolute { path = []; name } | Path.Local { name } -> name
  | _ -> assert false

let cst_path_name (c : DE.Term.Const.t) : string =
  path_name (DE.Term.Const.path c)

let rec term_uses_vars (vl : DE.Term.Var.t list) (t : DE.Term.t) : bool =
  match t.term_descr with
  | DE.Var v' -> List.exists (DE.Term.Var.equal v') vl
  | DE.Cst _ -> false
  | DE.App (f, _, args) ->
    term_uses_vars vl f || List.exists (term_uses_vars vl) args
  | DE.Binder (_, body) -> term_uses_vars vl body
  | _ -> false

let term_uses_all_vars (vl : DE.Term.Var.t list) (t : DE.Term.t) : bool =
  List.for_all (fun v -> term_uses_vars [v] t) vl
