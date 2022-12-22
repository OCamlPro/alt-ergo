
module DStd = Dolmen.Std
module Dl = Dolmen_loop

module State = Dl.State
module Pipeline = Dl.Pipeline.Make(State)

module Parser = Dolmen_loop.Parser.Make(State)
module Header = Dolmen_loop.Headers.Make(State)
module Typer = Dolmen_loop.Typer.Typer(State)
module Typer_Pipe =
  Dolmen_loop.Typer.Make(DStd.Expr)(DStd.Expr.Print)(State)(Typer)
