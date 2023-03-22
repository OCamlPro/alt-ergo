(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

module DStd = Dolmen.Std
module Dl = Dolmen_loop

module State = Dl.State
module Pipeline = Dl.Pipeline.Make(State)

module Parser = Dolmen_loop.Parser.Make(State)
module Header = Dolmen_loop.Headers.Make(State)
module Typer = Dolmen_loop.Typer.Typer(State)
module Typer_Pipe =
  Dolmen_loop.Typer.Make(DStd.Expr)(DStd.Expr.Print)(State)(Typer)
