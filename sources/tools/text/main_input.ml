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

(* === DOLMEN input method === *)

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

    module Void = struct
      type 'a t = unit
      let rwrt = ()
    end

    module W = struct
      type binding = [
        | `Not_found
        | `Ty of Ty.Safe.Const.t
        | `Term of Typed.Safe.Const.t
      ]

      let shadow _ _ _ = ()
      let unused_ty_var _ _ = ()
      let unused_term_var _ _ = ()
      let error_in_attribute _ _ = ()
      let not_found _ _ = ()
    end

    module T = Dolmen_type.Tff.Make(Void)(Ty.Safe)(Typed.Safe)(W)

    (* Dolmen's typing environment is not explicit, but stored
       in the global mutable state, hence no need for explicit
       environment. *)
    type env = unit
    let empty_env = ()


    (* Typing Builtins *)
    module B_tptp = Dolmen_type.Base.Tptp.Tff(T)(Ty.Safe)(Typed.Safe)
    module B_smtlib = Dolmen_type.Base.Smtlib.Tff(T)(Void)(Ty.Safe)(Typed.Safe)

    let builtins = function
      | L.Tptp -> B_tptp.parse
      | L.Smtlib -> B_smtlib.parse
      | _ -> (fun _ _ _ _ -> None)

    (* Starting environment (mainly to specify the builtins function) *)
    let start_env lang =
      let expect =
        match lang with
        | L.Tptp | L.Dimacs -> T.Typed Ty.Safe.prop
        | _ -> T.Nothing
      in
      T.empty_env ~expect (builtins lang)

    (* Get a location from a statement *)
    let _loc s =
      let module P = Dolmen.ParseLocation in
      match Dolmen.Statement.(s.loc) with
      | Some l -> Lexing.(
          { pos_fname = l.P.file; pos_lnum = l.P.start_line;
            pos_bol = 0; pos_cnum = l.P.start_column; },
          { pos_fname = l.P.file; pos_lnum = l.P.stop_line;
            pos_bol = 0; pos_cnum = l.P.stop_column; }
        )
      | None -> Lexing.dummy_pos, Lexing.dummy_pos

    (** Generate statement names *)
    let stmt_id ref_name =
      let counter = ref 0 in
      (fun c ->
         match c.Dolmen.Statement.id with
         | { Dolmen.Id.ns = Dolmen.Id.Decl; name = "" } ->
           let () = incr counter in
           Format.sprintf "%s_%d" ref_name !counter
         | id -> Dolmen.Id.full_name id)

    let hyp_id = stmt_id "hyp"


    (* Typecheck statements *)
    let rec type_parsed () (lang, s) =
      let module S = Dolmen.Statement in
      let l =
        match s.S.descr with
        | S.Pack l ->
          l
          |> List.map (fun s' -> (lang, s'))
          |> List.map (type_parsed ())
          |> List.map fst
          |> List.flatten
        (* Some statements, we just ignore .... *)
        | S.Set_info _ ->
          Format.eprintf "; ignoring set-info@.";
          []
        | S.Set_logic _ ->
          Format.eprintf "; ignoring set-logic@.";
          []
        (* Type declarations *)
        | S.Decl (id, ty) ->
          let env = start_env lang in
          begin match T.new_decl env ty id with
            | `Type_decl c ->
              [Typed.mk (Typed.TTypeDecl (_loc s, Ty.Safe.apply_empty c))]
            | `Term_decl c ->
              [Typed.mk (Typed.TLogic (_loc s,
                                       [Typed.Safe.Const.name c],
                                       Typed.Safe.Const.tlogic_type c))]
          end
        | S.Antecedent t ->
          let env = start_env lang in
          let e = T.parse env t in
          let _, ax = Typed.Safe.expect_prop e in
          [Typed.mk (Typed.TAxiom (_loc s, hyp_id s, Util.Default, ax))]
        | _ ->
          Format.eprintf "Error, don't know what to do with:@\n %a@." S.print s;
          exit 2
      in
      l, ()

    (* Error messages printing *)
    let () =
      let default_loc = Dolmen.ParseLocation.mk "<?>" 0 0 0 0 in
      let get_loc = function
        | Some loc -> loc
        | None -> default_loc
      in

      let pp_opt pp fmt = function
        | None -> ()
        | Some x -> pp fmt x
      in

      let pp_res fmt = function
        | T.Ttype -> Format.fprintf fmt "Ttype"
        | T.Ty ty -> Format.fprintf fmt "the type: %a" Ty.print ty
        | T.Term t -> Format.fprintf fmt "the term: %a" Typed.Safe.print t
        | T.Tags _ -> Format.fprintf fmt "a tag list"
      in

      let pp_err fmt = function
        | T.Infer_type_variable ->
          Format.fprintf fmt "Cannot infer the type of a variable"
        | T.Expected (s, r) ->
          Format.fprintf fmt "Expected %s, but got %a" s (pp_opt pp_res) r
        | T.Bad_op_arity (name, i, j) ->
          Format.fprintf fmt "Operator '%s' extects %d arguments but received %d" name i j
        | T.Bad_ty_arity (c, n) ->
          Format.fprintf fmt "Bad arity for id '%a': expected %d but got %d"
            Ty.Safe.Const.print c (Ty.Safe.Const.arity c) n
        | T.Bad_term_arity (c, n, m) ->
          let i, j = Typed.Safe.Const.arity c in
          Format.fprintf fmt "Bad arity for id '%a': expected %d/%d arguments but got %d/%d"
            Typed.Safe.Const.print c i j n m
        | T.Var_application v ->
          Format.fprintf fmt "Trying to apply variable '%a' to some arguments"
            Typed.Safe.Var.print v
        | T.Ty_var_application v ->
          Format.fprintf fmt "Trying to apply variable '%a' to some arguments"
            Ty.Safe.Var.print v
        | T.Type_mismatch (t, ty) ->
          Format.fprintf fmt "@[<hv>Term@ %a@ has type@ %a@ but was expected of type@ %a"
            Typed.Safe.print t Ty.print (Typed.Safe.ty t) Ty.print ty
        | T.Quantified_var_inference ->
          Format.fprintf fmt "Cannot infer the type of a quantified variable"
        | T.Unhandled_builtin b ->
          Format.fprintf fmt "The following dolmen primitive is unhandled: %a"
            Dolmen.Term.print_builtin b
        | T.Cannot_tag_tag ->
          Format.fprintf fmt "Internal error ?: Tags cannot be tagged"
        | T.Cannot_tag_ttype ->
          Format.fprintf fmt "The Ttype constant cannot be tagged"
        | T.Cannot_find d ->
          Format.fprintf fmt "The following couldn't be found in the environment: %a"
            Dolmen.Id.print d
        | T.Type_var_in_type_constructor ->
          Format.fprintf fmt "A type constructor's type cannot contain type variables"
        | T.Unhandled_ast ->
          Format.fprintf fmt "This AST constructor it not currently handled"
        | _ -> Format.fprintf fmt "Unknown error message, sorry :/"
      in

      Printexc.register_printer (function
          | Dolmen.ParseLocation.Uncaught (loc, exn) ->
            Some (
              Format.asprintf
                "%a:@\n%s@."
                Dolmen.ParseLocation.fmt loc (Printexc.to_string exn)
            )
          | Dolmen.ParseLocation.Lexing_error (loc, msg) ->
            Some (
              Format.asprintf
                "%a:@\nLexing error: invalid character '%s'@."
                Dolmen.ParseLocation.fmt loc msg
            )
          | Dolmen.ParseLocation.Syntax_error (loc, msg) ->
            Some (
              Format.asprintf
                "%a:@\n%s@."
                Dolmen.ParseLocation.fmt loc
                (match msg with "" -> "Syntax error" | x -> x)
            )

          | T.Typing_error (err, _, t) ->
            let loc = get_loc t.Dolmen.Term.loc in
            Some (
              Format.asprintf
                  "@[<hv>While typing:@ @[<hov>%a@]@]@.%a:@\n%a@."
                  Dolmen.Term.print t Dolmen.ParseLocation.fmt loc pp_err err
            )

          | _ -> None
        )
  end in
  Input.register "dolmen" (module M)

