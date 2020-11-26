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

    let parse_file ~file ~format =
      let l = Parsers.parse_problem_as_string ~file ~format in
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


(*
(* === DOLMEN input method === *)

let () =
  let module M : Input.S = struct

    (* Parsing *)

    module L = Dolmen.Logic.Make
        (Dolmen.ParseLocation)
        (Dolmen.Id)(Dolmen.Term)
        (Dolmen.Statement)

    type expr (* TODO: fill this *)

    type file = (L.language * Dolmen.Statement.t) list

    let parse_expr _ = assert false

    let parse_file ~filename ~preludes =
      let aux f =
        let lang, l = L.parse_file f in
        List.map (fun x -> lang, x) l
      in
      (* TODO: expand includes ? *)
      let l = List.concat (
          List.rev_map aux (filename :: List.rev preludes)
        ) in
      l


    (* Typechecking *)

    type env = unit

    let new_id () = 0

    let type_expr _ _ _ = assert false

    let type_file _ = [], ()

  end in
  Input.register "dolmen" (module M)
*)
