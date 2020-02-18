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
        | None ->
          close ();
          (* Dimancs need a special prove statement
             to be added at the end *)
          begin match lang with
            | L.Dimacs | L.Tptp ->
              let prove = Dolmen.Statement.prove () in
              Seq.Cons ((dir, lang, prove), Seq.empty)
            | _ ->
              Seq.Nil
          end
        | Some x -> Seq.Cons ((dir, lang, x), aux)
      in
      aux

    let parse_file (lang, dir, filename) : _ Seq.t =
      match L.find ~dir filename with
      | None -> raise Not_found
      | Some f ->
        begin match Dolmen.Misc.get_extension f with
          | ".zip" ->
            let f', contents = parse_zip f in
            let lang, _, _ = L.of_extension @@ Dolmen.Misc.get_extension f' in
            parse_aux dir @@ L.parse_input (`Raw (f', lang, contents))
          | _ ->
            let language =
              try let l, _, _ = L.of_filename f in Some l
              with L.Extension_not_found _ -> lang
            in
            parse_aux dir @@ L.parse_input ?language (`File f)
        end

    let parse_include (dir, lang, stmt) =
      match stmt with
      | { Dolmen.Statement.descr =
            Dolmen.Statement.Include file; _ } ->
        `Seq (parse_file (Some lang, dir, file))
      | _ -> `Ok

    let parse_files ~filename ~preludes =
      let l = preludes @ [filename] in
      Lists.to_seq l
      |> Seq.map (fun f -> None, Filename.dirname f, Filename.basename f)
      |> Seq.flat_map parse_file
      |> Seqs.flat_map_rec parse_include
      |> Seq.map (fun (_, l, stmt) -> (l, stmt))


    (* Typechecking *)

    module Void = struct
      type 'a t = unit
      let rwrt = ()

      type name = unit
      let name = ()
      let exact _ = ()

      type pos = unit
      let pos = ()
      let infix = ()
      let prefix = ()
    end

    module W = struct
      (* TODO: print warnings *)
      let shadow _ _ _ = ()
      let unused_ty_var _ _ = ()
      let unused_term_var _ _ = ()
      let error_in_attribute _ _ = ()
      let not_found _ _ = ()
      let superfluous_destructor _ _ _ _ = ()
    end

    module T = Dolmen_type.Tff.Make(Void)(Ty.Safe)(Typed.Safe)(W)

    (* Dolmen's typing environment is not explicit, but stored
       in a global mutable state, hence no need for explicit
       environment. *)
    type env = unit
    let empty_env = ()


    (* Typing Builtins *)
    module B_zf =
      Dolmen_type.Base.Zf.Tff(T)(Void)
    module B_tptp =
      Dolmen_type.Base.Tptp.Tff(T)(Ty.Safe)(Typed.Safe)
    module B_smtlib =
      Dolmen_type.Base.Smtlib.Tff(T)(Void)(Ty.Safe)(Typed.Safe)
    module B_smtlib_array =
      Dolmen_type.Arrays.Smtlib.Tff(T)(Ty.Safe)(Typed.Safe)
    module B_smtlib_bitv =
      Dolmen_type.Bitv.Smtlib.Tff(T)(Ty.Safe)(Typed.Safe)
    module B_smtlib_arith_int =
      Dolmen_type.Arith.Smtlib.Int.Tff(T)(Ty.Safe)(Typed.Safe.Int)
    module B_smtlib_arith_real =
      Dolmen_type.Arith.Smtlib.Real.Tff(T)(Ty.Safe)(Typed.Safe.Real)
    module B_smtlib_arith_real_int =
      Dolmen_type.Arith.Smtlib.Real_Int.Tff(T)(Ty.Safe)(Typed.Safe.Real_Int)

    let builtins = function
      | L.Tptp -> B_tptp.parse
      | L.Smtlib ->
        Dolmen_type.Base.merge [
          B_smtlib.parse;
          B_smtlib_array.parse;
          B_smtlib_bitv.parse;
          (* B_smtlib_arith_int.parse;
           * B_smtlib_arith_real.parse; *)
          B_smtlib_arith_real_int.parse;
        ]
      | L.Zf -> B_zf.parse
      | _ -> (fun _ _ _ _ -> None)

    (* Starting environment (mainly to specify the builtins function) *)
    let start_env lang =
      let expect =
        match lang with
        | L.Tptp | L.Dimacs -> T.Typed Ty.Safe.prop
        | _ -> T.Nothing
      in
      let infer_base =
        match lang with
        | L.Tptp -> Some Ty.Safe.base
        | L.Dimacs -> Some Ty.Safe.prop
        | _ -> None
      in
      T.empty_env ?infer_base ~expect (builtins lang)

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
    let goal_id = stmt_id "g"

    let type_form ?(negate=false) lang f =
      let env = start_env lang in
      let e =
        try T.parse env f
        with Typed.Safe.Wrong_type (t, ty) ->
          raise (T.Typing_error (T.Type_mismatch (t, ty), env, f))
      in
      let e' = if negate then Typed.Safe.neg e else e in
      let _, ax = Typed.Safe.expect_prop e' in
      ax

    let type_hyp s lang t =
      let ax = type_form lang t in
      [Typed.mk (Typed.TAxiom (_loc s, hyp_id s, Util.Default, ax))]

    let type_goal ~negate s lang g_sort t =
      let g = type_form ~negate lang t in
      let g' = Typed.monomorphize_form g in
      let name = Typed.fresh_hypothesis_name g_sort in
      [Typed.mk (Typed.TNegated_goal (_loc s, g_sort, name, g'))]

    let type_assumption s lang t =
      let f = type_form ~negate:false lang t in
      let not_f = Typed.(mk (TFop (OPnot, [f]))) in
      let g = Typed.monomorphize_form not_f in
      let g_sort = Typed.Cut in
      let hyp_name = Typed.fresh_hypothesis_name g_sort in
      [Typed.mk (Typed.TNegated_goal (_loc s, g_sort, goal_id s, g));
       Typed.mk (Typed.TAxiom (_loc s, hyp_name, Util.Default, f)) ]

    let get_role s =
      let module S = Dolmen.Statement in
      let module T = Dolmen.Term in
      match s.S.attr with
      | Some { T.term = T.Colon (_, {
          T.term = T.App (
              { T.term = T.Symbol f ; _ } , [
                { T.term = T.Symbol id; _ }
              ]) ; _ }) ; _ }
      | Some { T.term = T.App (
            { T.term = T.Symbol f ; _ } , [
              { T.term = T.Symbol id; _ }
            ]) ; _ }
        ->
        if Dolmen.Id.(equal tptp_role f) then
          Some (Dolmen.Id.full_name id)
        else
          None
      | _ -> None

    let is_tptp_assumption s = get_role s = Some "assumption"
    let is_tptp_negated_conjecture s = get_role s = Some "negated_conjecture"

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
        | S.Decls l ->
          let env = start_env lang in
          List.map (function
              | `Type_decl c ->
                Typed.mk (Typed.TTypeDecl (_loc s, Ty.Safe.apply_empty c))
              | `Term_decl c ->
                Typed.mk (Typed.TLogic (_loc s,
                                        [Typed.Safe.Const.name c],
                                        Typed.Safe.Const.tlogic_type c))
            ) (T.decls env l)
        (* Explicit Prove statements (aka check-sat in smtlib) *)
        | S.Prove [] ->
          begin match lang with
            | L.Smtlib | L.Dimacs | L.ICNF ->
              Options.set_unsat_mode true;
              let _, _false = Typed.Safe.(expect_prop @@ neg _true) in
              [Typed.mk (Typed.TNegated_goal
                           (_loc s, Typed.Thm, goal_id s, _false))]
            | _ -> []
          end
        (* Hypotheses *)
        | S.Antecedent t ->
          if is_tptp_assumption s then
            type_assumption s lang t
          else if is_tptp_negated_conjecture s then
            type_goal ~negate:true s lang Typed.Thm t
          else
            type_hyp s lang t
        | S.Consequent t ->
          type_goal ~negate:false s lang Typed.Thm t

        (* Special case for clauses *)
        | S.Clause l ->
          let env = start_env lang in
          let fv_lists = List.map Dolmen.Term.fv l in
          begin
            match List.sort_uniq Dolmen.Id.compare (List.flatten fv_lists) with
            | [] ->
              (* TODO: add a special case for clauses in type declaration,
                       to avoid encoding them using disjunctions. *)
              let l' = List.map (T.parse env) l in
              let _, ax = Typed.Safe.expect_prop @@ Typed.Safe._or l' in
              [Typed.mk (Typed.TAxiom (_loc s, hyp_id s, Util.Default, ax))]
            | free_vars ->
              (* if there are free variables, these must be quantified
                 or else the typchecker will raise an error. *)
              let loc = s.S.loc in
              let vars = List.map (Dolmen.Term.const ?loc) free_vars in
              let f = Dolmen.Term.forall ?loc vars (
                  match l with
                  | [] -> assert false | [p] -> p
                  | _ -> Dolmen.Term.apply ?loc (Dolmen.Term.or_t ?loc ()) l
                ) in
              let ax = type_form lang f in
              [Typed.mk (Typed.TAxiom (_loc s, hyp_id s, Util.Default, ax))]
          end
        | S.Exit ->
          exit 0
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
          Format.fprintf fmt
            "Operator '%s' extects %d arguments but received %d" name i j
        | T.Bad_ty_arity (c, n) ->
          Format.fprintf fmt "Bad arity for id '%a': expected %d but got %d"
            Ty.Safe.Const.print c (Ty.Safe.Const.arity c) n
        | T.Bad_term_arity (c, n, m) ->
          let i, j = Typed.Safe.Const.arity c in
          Format.fprintf fmt
            "Bad arity for id '%a': expected %d/%d arguments but got %d/%d"
            Typed.Safe.Const.print c i j n m
        | T.Var_application v ->
          Format.fprintf fmt "Trying to apply variable '%a' to some arguments"
            Typed.Safe.Var.print v
        | T.Ty_var_application v ->
          Format.fprintf fmt "Trying to apply variable '%a' to some arguments"
            Ty.Safe.Var.print v
        | T.Type_mismatch (t, ty) ->
          Format.fprintf fmt
            "@[<hv>Term@ %a@ has type@ %a@ but was expected of type@ %a"
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
          Format.fprintf fmt
            "The following couldn't be found in the environment: %a"
            Dolmen.Id.print d
        | T.Type_var_in_type_constructor ->
          Format.fprintf fmt
            "A type constructor's type cannot contain type variables"
        | T.Unhandled_ast ->
          Format.fprintf fmt "This AST constructor it not currently handled"
        | T.Unbound_variables (tys, ts, f) ->
          let pp_sep fmt () = Format.fprintf fmt ",@ " in
          Format.fprintf fmt "Unbound variables: %a@ %a@\nin: %a"
            (Format.pp_print_list ~pp_sep Ty.Safe.Var.print) tys
            (Format.pp_print_list ~pp_sep Typed.Safe.Var.print) ts
            Typed.Safe.print f
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

