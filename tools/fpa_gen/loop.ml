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

module State = struct
  include Dolmen_loop.State

  let is_interactive _ = false
end

module Pipeline = Dolmen_loop.Pipeline.Make (State)
module Parser = Dolmen_loop.Parser.Make (State)
module Header = Dolmen_loop.Headers.Make (State)
module Logic = Dolmen_loop.Logic

module Typer = struct
  module T = Dolmen_loop.Typer.Typer (State)
  include T
  include
    Dolmen_loop.Typer.Make (Dolmen.Std.Expr) (Dolmen.Std.Expr.Print) (State) (T)

  let init_pipe = init

  let init = T.init
end

module Export =
  Dolmen_loop.Export.Make (Dolmen.Std.Expr) (Dolmen_std.Term.View.Sexpr)
    (Dolmen_std.Expr.View.TFF)
    (State)
    (Typer)
