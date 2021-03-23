(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2018-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open AltErgoLib
open AltErgoParsers

(* === LEGACY input method === *)

let register_legacy () =
  let module M : Input.S = struct

    (* Parsing *)

    type parsed = Parsed.decl

    let parse_file ~content ~format =
      let l = Parsers.parse_problem_as_string ~content ~format in
      Lists.to_seq l

    let parse_files ~filename ~preludes =
      let l = Parsers.parse_problem ~filename ~preludes in
      Lists.to_seq l

    (* Typechecking *)

    include Typechecker

  end in
  (* Register the parser for natif format *)
  AltErgoParsers.Native_lexer.register_native ();
  (* Register the parser for smt2 format *)
  AltErgoParsers.Psmt2_to_alt_ergo.register_psmt2 ();
  (* Register the legacy frontend *)
  Input.register "legacy" (module M)
