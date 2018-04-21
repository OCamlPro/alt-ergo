(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

module Smtlib_error = Psmt2Frontend.Smtlib_error
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
  (**************************************************************************)
  let translate_left_assoc f id params =
    match params with
    | [] | [_] -> assert false
    | t :: l ->
      List.fold_left (fun acc t ->
          f id.p acc t
        ) t l

  let translate_right_assoc f id params =
    match List.rev params with
    | [] | [_] -> assert false
    | t :: l ->
      List.fold_left (fun acc t ->
          f id.p t acc
        ) t l

  let translate_chainable_assoc f id params =
    match params with
    | [] | [_] -> assert false
    | a::b::l ->
      let (res,_) = List.fold_left (fun (acc,curr) next ->
          mk_and id.p acc (f id.p curr next), next
        ) ((f id.p a b),b) l
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
      | TArray (t1,t2) -> mk_external_type sort.p [aux t1;aux t2] "farray"
      | TBitVec (n) -> assert false
      | TSort (s,t_list) -> mk_external_type sort.p (List.map aux t_list) s
      | TDatatype (d,t_list) -> assert false
      | TVar (s) -> mk_var_type sort.p s
      | TFun (t_list,t) -> assert false
      | TLink(t) -> assert false
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
    let loc = t.p in
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
    | Const_Str(s) -> assert false (* to do *)
    | Const_Hex(s) -> mk_int_const loc s
    | Const_Bin(s) -> mk_int_const loc s

  let translate_identifier id params raw_params =
    let name = Smtlib_typed_env.get_identifier id in
    match name.c with
    | "true" -> mk_true_const name.p
    | "false" -> mk_false_const name.p
    | "+" -> begin
        match params with
        | [p] -> p
        | _ -> translate_left_assoc mk_add name params
      end
    | "-" -> begin
        match params with
        | [t] -> mk_minus name.p t
        | _ -> translate_left_assoc mk_sub name params
      end
    | "*" -> translate_left_assoc mk_mul name params
    | "/" -> translate_left_assoc mk_div name params
    | "div" -> translate_left_assoc mk_div name params
    | "mod" -> begin
        match params with
        | [t1;t2] -> mk_mod name.p t1 t2
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
        | [b;e1;e2] -> mk_ite name.p b e1 e2
        | _ -> assert false
      end
    | "not" -> begin
        match params with
        | [t] -> mk_not name.p t
        | _ -> assert false
      end
    | "distinct" -> mk_distinct name.p params
    | "select" -> begin
        match params with
        | [t;i] -> mk_array_get name.p t i
        | _ -> assert false
      end
    | "store" -> begin
        match params with
        | [t;i;j] -> mk_array_set name.p t i j
        | _ -> assert false
      end
    | _ ->
      if name.is_quantif then
        mk_var name.p name.c
      else
        mk_application name.p name.c params

  let translate_qual_identifier qid params raw_params=
    match qid.c with
    | QualIdentifierId(id) -> translate_identifier id params raw_params, None
    | QualIdentifierAs(id,sort) ->
      translate_identifier id params raw_params, Some sort

  let rec translate_key_term pars acc k =
    match k.c with
    | Pattern(term_list) ->
      let tl = List.map (translate_term pars) term_list in
      (tl, false) :: acc
    | Named(symb) ->
      if Options.verbose () then
        Printf.eprintf "[Warning] (! :named not yet supported)\n%!";
      acc

  and translate_quantif f svl pars t =
    match t.c with
    | TermExclimationPt(term,key_term_list) ->
      let triggers = List.fold_left (fun acc key_term ->
          translate_key_term pars acc key_term
        ) [] key_term_list in
      f t.p svl triggers [] (translate_term pars term)
    | _ -> f t.p svl [] [] (translate_term pars t)

  and translate_term pars term =
    match term.c with
    | TermSpecConst(cst) -> translate_constant cst term
    | TermQualIdentifier(qid) ->
      let q,s = translate_qual_identifier qid [] [] in
      begin
        match s with
        | None -> q
        | Some s -> mk_type_cast term.p q (translate_sort s)
      end
    | TermQualIdTerm(qid,term_list) ->
      let params = List.map (translate_term pars) term_list in
      let q,s = translate_qual_identifier qid params term_list in
      begin
        match s with
        | None -> q
        | Some s -> mk_type_cast term.p q (translate_sort s)
      end
    | TermLetTerm(varbinding_list,term) ->
      let varbind = List.map (fun (s,term) ->
          s.c, (translate_term pars term)
        ) varbinding_list in
      mk_let term.p varbind (translate_term pars term)
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
    | TermExclimationPt(term,key_term_list) ->
      translate_term pars term
    | TermMatch(term,pattern_term_list) -> assert false

  let translate_assert_term (pars,term) =
    translate_term pars term

  let translate_goal pos (pars,term) =
    mk_goal pos "g" (translate_assert_term (pars,term))

  let translate_assert =
    let cpt = ref 0 in
    fun pos (pars,term) ->
      incr cpt;
      let name = Printf.sprintf "ax__%d" !cpt in
      mk_generic_axiom pos name (translate_assert_term (pars,term))

  let translate_const_dec (_,sort) =
    translate_sort sort

  let translate_decl_fun f params ret =
    let logic_type = mk_logic_type params (Some ret) in
    mk_logic f.p Symbols.Other [(f.c,f.c)] logic_type

  let translate_fun_dec (_,sl,s) =
    List.map translate_sort sl, translate_sort s

  let translate_fun_def_aux (symb,pars,svl,sort) =
    let pars = List.map (fun par -> par.c) pars in
    let params = List.map (fun (p,s) -> p.p,p.c,translate_sort s) svl in
    symb, params, translate_sort sort, pars

  let translate_fun_def fun_def term =
    let symb,params,ret,pars = translate_fun_def_aux fun_def in
    let t_expr = translate_term pars term in
    if Smtlib_ty.is_bool (Smtlib_ty.shorten term.ty) then
      mk_non_ground_predicate_def  symb.p (symb.c,symb.c) params t_expr
    else mk_function_def symb.p (symb.c,symb.c) params ret t_expr

  let translate_command acc command =
    match command.c with
    | Cmd_Assert(assert_term) ->
      (translate_assert command.p assert_term) :: acc
    | Cmd_CheckEntailment(assert_term) ->
      Options.set_unsat_mode false;
      (translate_goal command.p assert_term) :: acc
    | Cmd_CheckSat ->
      Options.set_unsat_mode true;
      (mk_goal command.p "g" (mk_false_const command.p)) :: acc
    | Cmd_CheckSatAssum prop_lit_list  ->
      Format.eprintf "Not yet supported@."; assert false
    | Cmd_DeclareConst(symbol,const_dec) ->
      (translate_decl_fun symbol [] (translate_const_dec const_dec)) :: acc
    | Cmd_DeclareDataType(symbol,datatype_dec) -> assert false
    | Cmd_DeclareDataTypes(sort_dec_list,datatype_dec_list) -> assert false
    | Cmd_DeclareFun(symbol,fun_dec) ->
      let params,ret = translate_fun_dec fun_dec in
      (translate_decl_fun symbol params ret):: acc
    | Cmd_DeclareSort(symbol,n) ->
      let n = int_of_string n in
      let pars = init n (fun i -> Printf.sprintf "'a_%d" i) in
      (mk_abstract_type_decl command.p pars symbol.c) :: acc
    | Cmd_DefineFun(fun_def,term)
    | Cmd_DefineFunRec(fun_def,term) ->
      (translate_fun_def fun_def term) :: acc
    | Cmd_DefineFunsRec(fun_def_list,term_list) ->
      let l = List.map2 translate_fun_def fun_def_list term_list in
      l @ acc
    | Cmd_DefineSort(symbol,symbol_list,sort) -> acc
    | Cmd_Echo(attribute_value) -> Format.eprintf "Not yet supported@."; acc
    | Cmd_GetAssert -> Format.eprintf "Not yet supported@."; acc
    | Cmd_GetProof -> Format.eprintf "Not yet supported@."; acc
    | Cmd_GetUnsatCore -> Format.eprintf "Not yet supported@."; acc
    | Cmd_GetValue(term_list) -> Format.eprintf "Not yet supported@."; acc
    | Cmd_GetAssign -> Format.eprintf "Not yet supported@."; acc
    | Cmd_GetOption(keyword) -> Format.eprintf "Not yet supported@."; acc
    | Cmd_GetInfo(key_info) -> Format.eprintf "Not yet supported@."; acc
    | Cmd_GetModel -> Format.eprintf "Not yet supported@."; acc
    | Cmd_GetUnsatAssumptions -> Format.eprintf "Not yet supported@."; acc
    | Cmd_Reset -> Format.eprintf "Not yet supported@."; assert false
    | Cmd_ResetAssert -> Format.eprintf "Not yet supported@."; assert false
    | Cmd_SetLogic(symbol) -> Format.eprintf "Not yet supported@."; acc
    | Cmd_SetOption(option) -> Format.eprintf "Not yet supported@."; acc
    | Cmd_SetInfo(attribute) -> Format.eprintf "Not yet supported@."; acc
    | Cmd_Push(string) -> Format.eprintf "Not yet supported@."; assert false
    | Cmd_Pop(string) -> Format.eprintf "Not yet supported@."; assert false
    | Cmd_Exit -> acc

  let init () =
    if Smtlib_error.get_is_int_real () then
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

    if Options.type_smt2 () then
      []
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
