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

open AltErgoLib
open AltErgoParsers

(* === LEGACY input method === *)

let () =
  let module M : Input.S = struct

    (* Parsing *)

    type parsed = Parsed.decl

    let parse_files ~filename ~preludes =
      let l = Parsers.parse_problem ~filename ~preludes in
      Lists.to_seq l

    (** Typechecking *)

    include Typechecker

  end in
  Input.register "legacy" (module M)

(* === DOLMEN inut method === *)

let () =
  let module M : Input.S = struct

    (* Parsing *)

    module L = Dolmen.Logic.Make
        (Dolmen.ParseLocation)
        (Dolmen.Id)(Dolmen.Term)
        (Dolmen.Statement)

    type parsed = L.language * Dolmen.Statement.t

    let parse_zip f =
      let ch = MyZip.open_in f in
      try
        match MyZip.entries ch with
        | [e] when not (MyZip.is_directory e) ->
          let contents = MyZip.read_entry ch e in
          let filename = MyZip.filename e in
          MyZip.close_in ch;
          filename, contents
        | _ ->
          MyZip.close_in ch;
          raise (Arg.Bad
                   (Format.asprintf "%s '%s' %s@?"
                      "The zipped file" f
                      "should contain exactly one file."))
      with e ->
        MyZip.close_in ch;
        raise e

    let parse_aux dir (lang, gen, close) =
      let rec aux () =
        match gen () with
        | None -> close (); Seq.Nil
        | Some x -> Cons ((dir, lang, x), aux)
      in
      aux

    let parse_file (dir, filename) : _ Seq.t =
      match L.find ~dir filename with
      | None -> raise Not_found
      | Some f ->
        begin match Dolmen.Misc.get_extension f with
          | ".zip" ->
            let f', contents = parse_zip f in
            let lang, _, _ = L.of_extension @@ Dolmen.Misc.get_extension f' in
            parse_aux dir @@ L.parse_input (`Raw (f', lang, contents))
          | _ ->
            parse_aux dir @@ L.parse_input (`File f)
        end

    let parse_include (dir, _, stmt) =
      match stmt with
      | { Dolmen.Statement.descr =
            Dolmen.Statement.Include file; _ } ->
        `Seq (parse_file (dir, file))
      | _ -> `Ok

    let parse_files ~filename ~preludes =
      let l = preludes @ [filename] in
      Lists.to_seq l
      |> Seq.map (fun f -> Filename.dirname f, Filename.basename f)
      |> Seq.flat_map parse_file
      |> Seqs.flat_map_rec parse_include
      |> Seq.map (fun (_, l, stmt) -> (l, stmt))


    (* Typechecking *)

    type env = unit

    let empty_env = ()

    let type_parsed () _ = assert false

  end in
  Input.register "dolmen" (module M)

