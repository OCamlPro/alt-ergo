(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open AltErgoLib

module Smtlib_error = Psmt2Frontend.Smtlib_error
module Smtlib_options = Psmt2Frontend.Options
module Smtlib_ty = Psmt2Frontend.Smtlib_ty
module Smtlib_typed_env = Psmt2Frontend.Smtlib_typed_env
module Smtlib_typing = Psmt2Frontend.Smtlib_typing
module Smtlib_syntax = Psmt2Frontend.Smtlib_syntax
module Smtlib_parser = Psmt2Frontend.Smtlib_parser
module Smtlib_lexer = Psmt2Frontend.Smtlib_lexer

open Smtlib_syntax
open Options
open Parsed_interface


module Translate = struct

  let pos x =
    match x.p with
    | None -> Loc.dummy
    | Some p -> p

  (**************************************************************************)
  let translate_left_assoc f id params =
    match params with
    | [] | [_] -> assert false
    | t :: l ->
      List.fold_left (fun acc t ->
          f (pos id) acc t
        ) t l

  let translate_right_assoc f id params =
    match List.rev params with
    | [] | [_] -> assert false
    | t :: l ->
      List.fold_left (fun acc t ->
          f (pos id) t acc
        ) t l

  let translate_chainable_assoc f id params =
    match params with
    | [] | [_] -> assert false
    | a::b::l ->
      let (res,_) = List.fold_left (fun (acc,curr) next ->
          mk_and (pos id) acc (f (pos id) curr next), next
        ) ((f (pos id) a b),b) l
      in res

  (**************************************************************************)
  let init n f =
    let rec init_aux i n f =
      if i >= n then []
      else
        let r = f i in
        r :: init_aux (i+1) n f
    in
    init_aux 0 n f

  let translate_sort sort =
    let open Smtlib_ty in
    let rec aux ty =
      match (shorten ty).desc with
      | TDummy -> assert false
      | TInt -> int_type
      | TReal -> real_type
      | TBool -> bool_type
      | TString -> assert false
      | TArray (t1,t2) -> mk_external_type (pos sort) [aux t1;aux t2] "farray"
      | TBitVec _ -> assert false
      | TSort (s,t_list) -> mk_external_type (pos sort) (List.map aux t_list) s
      | TDatatype (d,t_list) ->
        mk_external_type (pos sort) (List.map aux t_list) d
      | TVar (s) -> mk_var_type (pos sort) s
      | TFun _ -> assert false
      | TLink _ -> assert false
      | TRoundingMode -> assert false
      | TFloatingPoint _ -> assert false
    in
    aux sort.ty

  let better_num_of_string s =
    begin match String.split_on_char '.' s with
      | [n] | [n;""] -> Num.num_of_string n
      | [n; d] ->
        let l = String.length d in
        let n = if (String.length n) = 0 then Num.Int 0
          else Num.num_of_string n in
        let d = Num.num_of_string d in
        let e = Num.power_num (Num.Int 10) (Num.Int l) in
        Num.add_num n (Num.div_num d e)
      | _ -> assert false
    end

  let translate_constant cst t =
    let loc = pos t in
    match cst with
    | Const_Dec(s) -> mk_real_const loc (better_num_of_string s)
    | Const_Num(s) ->
      let open Smtlib_ty in
      let ty = shorten t.ty in
      begin match ty.desc with (*TODO: do shorten earlier and better*)
        | TInt  -> mk_int_const loc s
        | TReal -> mk_real_const loc (better_num_of_string s)
        | _ ->
          Format.eprintf "%s@." (to_string ty);
          assert false
      end
    | Const_Str _  -> assert false (* to do *)
    | Const_Hex(s) -> mk_int_const loc s
    | Const_Bin(s) -> mk_int_const loc s

  let translate_string_identifier name params raw_params =
    match name.c with
    | "true" -> mk_true_const (pos name)
    | "false" -> mk_false_const (pos name)
    | "+" -> begin
        match params with
        | [p] -> p
        | _ -> translate_left_assoc mk_add name params
      end
    | "-" -> begin
        match params with
        | [t] -> mk_minus (pos name) t
        | _ -> translate_left_assoc mk_sub name params
      end
    | "*" -> translate_left_assoc mk_mul name params
    | "/" -> translate_left_assoc mk_div name params
    | "div" -> translate_left_assoc mk_div name params
    | "mod" -> begin
        match params with
        | [t1;t2] -> mk_mod (pos name) t1 t2
        | _ -> assert false
      end
    | "abs" -> begin
        match params with
        | [x] ->
          let cond = mk_pred_ge (pos name) x (mk_int_const (pos name) "0") in
          mk_ite (pos name) cond x (mk_minus (pos name) x)
        | _ -> assert false
      end
    | "<" -> translate_chainable_assoc mk_pred_lt name params
    | "<=" -> translate_chainable_assoc mk_pred_le name params
    | ">" -> translate_chainable_assoc mk_pred_gt name params
    | ">=" -> translate_chainable_assoc mk_pred_ge name params
    | "=" ->
      let f = match raw_params with
        | [] -> assert false
        | par :: _ ->
          if Smtlib_ty.is_bool (Smtlib_ty.shorten par.ty) then mk_iff
          else mk_pred_eq
      in
      translate_chainable_assoc f name params
    | "=>" -> translate_right_assoc mk_implies name params
    | "and" -> begin
        match params with
        | [p] -> p
        | _ -> translate_left_assoc mk_and name params
      end
    | "or" -> begin
        match params with
        | [p] -> p
        | _ -> translate_left_assoc mk_or name params
      end
    | "xor" -> translate_left_assoc mk_xor name params
    | "ite" ->
      begin
        match params with
        | [b;e1;e2] -> mk_ite (pos name) b e1 e2
        | _ -> assert false
      end
    | "not" -> begin
        match params with
        | [t] -> mk_not (pos name) t
        | _ -> assert false
      end
    | "distinct" -> mk_distinct (pos name) params
    | "select" -> begin
        match params with
        | [t;i] -> mk_array_get (pos name) t i
        | _ -> assert false
      end
    | "store" -> begin
        match params with
        | [t;i;j] -> mk_array_set (pos name) t i j
        | _ -> assert false
      end
    | _ ->
      if name.is_quantif then
        mk_var (pos name) name.c
      else
        mk_application (pos name) name.c params



  let translate_identifier id params raw_params =
    let name, l = Smtlib_typed_env.get_identifier id in
    match name.c, l, params with
    | _, [], _ -> translate_string_identifier name params raw_params
    | "is", [constr], [e] ->
      mk_algebraic_test (pos name) e constr
    | _ ->
      Format.eprintf "TODO: handle other underscored IDs@.";
      assert false

  let translate_qual_identifier qid params raw_params=
    match qid.c with
    | QualIdentifierId(id) -> translate_identifier id params raw_params, None
    | QualIdentifierAs(id,sort) ->
      translate_identifier id params raw_params, Some sort

  let rec translate_key_term pars acc k =
    match k.c with
    | Pattern(term_list) ->
      let tl = List.map (translate_term pars) term_list in
      (tl, true) :: acc
    | Named _ ->
      if Options.verbose () then
        Printf.eprintf "[Warning] (! :named not yet supported)\n%!";
      acc

  and translate_quantif f svl pars t =
    match t.c with
    | TermExclimationPt(term,key_term_list) ->
      let triggers = List.fold_left (fun acc key_term ->
          translate_key_term pars acc key_term
        ) [] key_term_list in
      f (pos t) svl triggers [] (translate_term pars term)
    | _ -> f (pos t) svl [] [] (translate_term pars t)

  and translate_term pars term =
    match term.c with
    | TermSpecConst(cst) -> translate_constant cst term
    | TermQualIdentifier(qid) ->
      let q,s = translate_qual_identifier qid [] [] in
      begin
        match s with
        | None -> q
        | Some s -> mk_type_cast (pos term) q (translate_sort s)
      end
    | TermQualIdTerm(qid,term_list) ->
      let params = List.map (translate_term pars) term_list in
      let q,s = translate_qual_identifier qid params term_list in
      begin
        match s with
        | None -> q
        | Some s -> mk_type_cast (pos term) q (translate_sort s)
      end
    | TermLetTerm(varbinding_list,term) ->
      let varbind = List.map (fun (s,term) ->
          s.c, (translate_term pars term)
        ) varbinding_list in
      mk_let (pos term) varbind (translate_term pars term)
    | TermForAllTerm(sorted_var_list,t) ->
      let svl = List.map (fun (v,s) ->
          v.c, v.c, translate_sort s
        ) sorted_var_list in
      translate_quantif mk_forall svl pars t
    | TermExistsTerm(sorted_var_list,t) ->
      let svl = List.map (fun (v,s) ->
          v.c, "", translate_sort s
        ) sorted_var_list in
      translate_quantif mk_exists svl pars t
    | TermExclimationPt(term,_key_term_list) ->
      translate_term pars term
    | TermMatch(term,pattern_term_list) ->
      let t = translate_term pars term in
      let cases = List.map (fun (pat,term) ->
          translate_pattern pat,
          translate_term pars term
        ) pattern_term_list
      in
      mk_match (pos term) t cases

  and translate_pattern pat =
    let p = pos pat in
    match pat.c with
    | MatchPattern(s,sl) -> mk_pattern p s.c (List.map (fun s -> s.c) sl)
    | MatchUnderscore -> mk_pattern p "_" []

  let translate_assert_term (pars,term) =
    translate_term pars term

  let translate_goal pos (pars,term) =
    mk_goal pos "g" (translate_assert_term (pars,term))

  let name_of_assert term =
    match term.c with
    | TermExclimationPt(_, [{ c = Named s; _ }]) -> Some s.c
    | _ -> None

  let translate_assert =
    let cpt = ref 0 in
    fun pos (pars,term) ->
      incr cpt;
      let name =
        match name_of_assert term with
        | Some s -> s
        | None -> Printf.sprintf "unamed__assert__%d" !cpt
      in
      mk_generic_axiom pos name (translate_assert_term (pars,term))

  let translate_const_dec (_,sort) =
    translate_sort sort

  let translate_decl_fun f params ret =
    let logic_type = mk_logic_type params (Some ret) in
    mk_logic (pos f) Symbols.Other [(f.c,f.c)] logic_type

  let translate_fun_dec (_,sl,s) =
    List.map translate_sort sl, translate_sort s

  let translate_fun_def_aux (symb,pars,svl,sort) =
    let pars = List.map (fun par -> par.c) pars in
    let params = List.map (fun (p,s) -> pos p, p.c,translate_sort s) svl in
    symb, params, translate_sort sort, pars

  let translate_fun_def fun_def term =
    let symb,params,ret,pars = translate_fun_def_aux fun_def in
    let t_expr = translate_term pars term in
    if Smtlib_ty.is_bool (Smtlib_ty.shorten term.ty) then
      mk_non_ground_predicate_def (pos symb) (symb.c,symb.c) params t_expr
    else mk_function_def (pos symb) (symb.c,symb.c) params ret t_expr

  let translate_datatype_decl (name, _) (params, cases) =
    let params = List.map (fun n -> n.c) params in
    let cases =
      List.map (fun (constr, d_l) ->
          constr.c,
          List.map (fun (des, sort) -> des.c, translate_sort sort) d_l
        )cases
    in
    pos name, params, name.c, (Parsed.Algebraic cases)

  let translate_datatypes sort_dec datatype_dec =
    try
      mk_rec_type_decl @@
      List.map2 translate_datatype_decl sort_dec datatype_dec
    with Invalid_argument _ -> assert false

  let not_supported s =
    Format.eprintf "; %S : Not yet supported@." s

  let translate_command acc command =
    match command.c with
    | Cmd_Assert(assert_term) ->
      (translate_assert (pos command) assert_term) :: acc
    | Cmd_CheckEntailment(assert_term) ->
      Options.set_unsat_mode false;
      (translate_goal (pos command) assert_term) :: acc
    | Cmd_CheckSat ->
      Options.set_unsat_mode true;
      (mk_goal (pos command) "g" (mk_false_const (pos command))) :: acc
    | Cmd_CheckSatAssum _ ->
      not_supported "check-sat-assuming"; assert false
    | Cmd_DeclareConst(symbol,const_dec) ->
      (translate_decl_fun symbol [] (translate_const_dec const_dec)) :: acc
    | Cmd_DeclareDataType(symbol,datatype_dec) ->
      (mk_rec_type_decl
         [(translate_datatype_decl (symbol,0) datatype_dec)]) :: acc
    | Cmd_DeclareDataTypes(sort_dec_list,datatype_dec_list) ->
      (translate_datatypes sort_dec_list datatype_dec_list) :: acc

    | Cmd_DeclareFun(symbol,fun_dec) ->
      let params,ret = translate_fun_dec fun_dec in
      (translate_decl_fun symbol params ret):: acc
    | Cmd_DeclareSort(symbol,n) ->
      let n = int_of_string n in
      let pars = init n (fun i -> Printf.sprintf "'a_%d" i) in
      (mk_abstract_type_decl (pos command) pars symbol.c) :: acc
    | Cmd_DefineFun(fun_def,term)
    | Cmd_DefineFunRec(fun_def,term) ->
      (translate_fun_def fun_def term) :: acc
    | Cmd_DefineFunsRec(fun_def_list,term_list) ->
      let l = List.map2 translate_fun_def fun_def_list term_list in
      l @ acc
    | Cmd_DefineSort _ -> acc
    | Cmd_Echo _ -> not_supported "echo"; acc
    | Cmd_GetAssert -> not_supported "get-assertions"; acc
    | Cmd_GetProof -> not_supported "get-proof"; acc
    | Cmd_GetUnsatCore -> not_supported "get-unsat-core"; acc
    | Cmd_GetValue _ -> not_supported "get-value"; acc
    | Cmd_GetAssign -> not_supported "get-assign"; acc
    | Cmd_GetOption _ -> not_supported "get-option"; acc
    | Cmd_GetInfo _ -> not_supported "get-info"; acc
    | Cmd_GetModel -> not_supported "get-model"; acc
    | Cmd_GetUnsatAssumptions -> not_supported "get-unsat-assumptions"; acc
    | Cmd_Reset -> not_supported "reset"; assert false
    | Cmd_ResetAssert -> not_supported "reset-asserts"; assert false
    | Cmd_SetLogic _ -> not_supported "set-logic"; acc
    | Cmd_SetOption _ -> not_supported "set-option"; acc
    | Cmd_SetInfo _ -> not_supported "set-info"; acc
    | Cmd_Push _ -> not_supported "push"; assert false
    | Cmd_Pop _ -> not_supported "pop"; assert false
    | Cmd_Exit -> acc

  let init () =
    if Psmt2Frontend.Options.get_is_int_real () then
      let dummy_pos = Lexing.dummy_pos,Lexing.dummy_pos in

      (* assert false; *)
      let logic_type = mk_logic_type [real_type] (Some int_type) in
      let to_int =
        mk_logic dummy_pos Symbols.Other [("to_int","to_int")] logic_type in
      let logic_type = mk_logic_type [int_type] (Some real_type) in
      let to_real =
        mk_logic dummy_pos Symbols.Other [("to_real","to_real")] logic_type in
      let logic_type = mk_logic_type [real_type] (Some bool_type) in
      let is_int =
        mk_logic dummy_pos Symbols.Other [("is_int","is_int")] logic_type in
      [to_int;to_real;is_int]
    else []

  let file commands =
    Smtlib_typing.typing commands;

    if Options.type_smt2 () then begin
      Printf.eprintf "%s%!" (Smtlib_options.status ());
      []
    end
    else begin
      let l = List.fold_left translate_command [] (List.rev commands) in
      (init ()) @ l
    end

  let lexpr l = translate_term [] l

  let trigger (tl,b) = List.map (translate_term []) tl,b

end

let aux aux_fun token lexbuf =
  try
    let res = aux_fun token lexbuf in
    Parsing.clear_parser ();
    res
  with
  | Parsing.Parse_error
  | (*Basics. | MenhirBasics. |*) Smtlib_error.Error _ ->
    (* not fully qualified ! backward incompat. in Menhir !!*)
    let loc = (Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf) in
    let lex = Lexing.lexeme lexbuf in
    Parsing.clear_parser ();
    raise (Errors.Syntax_error (loc, lex))

let file_parser token lexbuf =
  Translate.file (Smtlib_parser.commands token lexbuf)

let lexpr_parser token lexbuf =
  Translate.lexpr (Smtlib_parser.term token lexbuf)

let trigger_parser token lexbuf =
  Translate.trigger (Smtlib_parser.term_list token lexbuf)

module Parser : Parsers.PARSER_INTERFACE = struct
  let file    = aux file_parser    Smtlib_lexer.token
  let expr    = aux lexpr_parser   Smtlib_lexer.token
  let trigger = aux trigger_parser Smtlib_lexer.token
end

let () =
  (*register this parser in Input_lang: 2 different extensions recognized *)
  let p = (module Parser : Parsers.PARSER_INTERFACE) in
  Parsers.register_parser ~lang:".smt2" p;
  Parsers.register_parser ~lang:".psmt2" p;
