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

open AltErgoLib
open AltErgoParsers

(* === LEGACY input method === *)

let register_legacy () =
  let module M : Input.S with type parsed = Parsed.decl = struct

    (* Parsing *)

    type parsed = Parsed.decl

    let parse_file ~content ~format =
      let l = Parsers.parse_problem_as_string ~content ~format in
      Stdcompat.List.to_seq l

    let parse_files ~filename ~preludes =
      let l = Parsers.parse_problem ~filename ~preludes in
      Stdcompat.List.to_seq l

    (* Typechecking *)

    include Typechecker

  end in
  (* Register the parser for natif format *)
  AltErgoParsers.Native_lexer.register_native ();
  (* Register the parser for smt2 format *)
  AltErgoParsers.Psmt2_to_alt_ergo.register_psmt2 ();
  (* Register the legacy frontend *)
  Input.register "legacy" (module M)
