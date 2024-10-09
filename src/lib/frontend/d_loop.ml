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

module Dl = Dolmen_loop
open Alias.Dolmen

module State = struct
  include Dl.State

  (* Overriding error function so that error does not savagely exit. *)
  let error ?file ?loc st error payload =
    let st = flush st () in
    let loc = DStd.Misc.opt_map loc DStd.Loc.full_loc in
    let aux _ =
      let code, descr = Dl.(Code.descr Dl.Report.Error.(code error)) in
      raise (Errors.(error (Dolmen_error (code, descr))))
    in
    match get report_style st with
    | Minimal ->
      Format.kfprintf aux Format.err_formatter
        "E:%s@." (Dl.Report.Error.mnemonic error)
    | Regular | Contextual ->
      Format.kfprintf aux Format.err_formatter
        ("@[<v>%a%a @[<hov>%a@]%a@]@.")
        (pp_loc ?file st) loc
        Fmt.(styled `Bold @@ styled (`Fg (`Hi `Red)) string) "Error"
        Dl.Report.Error.print (error, payload)
        Dl.Report.Error.print_hints (error, payload)
end

module Pipeline = Dl.Pipeline.Make(State)
module Parser = Dl.Parser.Make(State)
module Header = Dl.Headers.Make(State)
module Typer = Dl.Typer.Typer(State)
module Typer_Pipe = Dolmen_loop.Typer.Make(DE)(DE.Print)(State)(Typer)
