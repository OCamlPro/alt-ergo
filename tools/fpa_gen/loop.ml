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
