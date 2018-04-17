open Options
open Parsed_interface
open Smtlib_syntax

(******************************************************************************)
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

(******************************************************************************)
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
    let varbind = List.map (fun varb ->
        let s,term = varb.c in
        s.c, (translate_term pars term)
      ) varbinding_list in
    mk_let term.p varbind (translate_term pars term)
  | TermForAllTerm(sorted_var_list,t) ->
    let svl = List.map (fun sv ->
        let v,s = sv.c in
        v.c, v.c, translate_sort s
      ) sorted_var_list in
    translate_quantif mk_forall svl pars t
  | TermExistsTerm(sorted_var_list,t) ->
    let svl = List.map (fun sv ->
        let v,s = sv.c in
        v.c, "", translate_sort s
      ) sorted_var_list in
    translate_quantif mk_exists svl pars t
  | TermExclimationPt(term,key_term_list) ->
    translate_term pars term
  | TermMatch(term,pattern_term_list) -> assert false

let translate_assert_term at =
  match at.c with
  | Assert_dec(term) -> translate_term [] term
  | Assert_dec_par(pars,term) ->
    let pars = List.map (fun par -> par.c) pars in
    translate_term pars term

let translate_goal at =
  mk_goal at.p "g" (translate_assert_term at)

let translate_assert =
  let cpt = ref 0 in
  fun at ->
    incr cpt;
    let name = Printf.sprintf "ax__%d" !cpt in
    mk_generic_axiom at.p name (translate_assert_term at)

let translate_const_dec cst =
  match cst.c with
  | Const_dec_sort t -> translate_sort t
  | Const_dec_par (_,t) -> translate_sort t

let translate_decl_fun f params ret =
  let logic_type = mk_logic_type params (Some ret) in
  mk_logic f.p Symbols.Other [(f.c,f.c)] logic_type

let translate_fun_dec fun_dec =
  match fun_dec.c with
  | Fun_dec (sl,s) -> List.map translate_sort sl, translate_sort s
  | Fun_dec_par (_,sl,s) ->
    List.map translate_sort sl, translate_sort s

let translate_fun_def fun_def =
  match fun_def.c with
  | Fun_def (symb,svl,sort) ->
    symb,
    List.map (fun sv -> let p,s = sv.c in p.p,p.c,translate_sort s) svl,
    translate_sort sort, []
  | Fun_def_par (symb,pars,svl,sort) ->
    let pars = List.map (fun par -> par.c) pars in
    symb,
    List.map (fun sv -> let p,s = sv.c in p.p,p.c,translate_sort s) svl,
    translate_sort sort,pars

let translate_fun_def fun_def term =
  let symb,params,ret,pars = translate_fun_def fun_def in
  let t_expr = translate_term pars term in
  if Smtlib_ty.is_bool (Smtlib_ty.shorten term.ty) then
    mk_non_ground_predicate_def  symb.p (symb.c,symb.c) params t_expr
  else mk_function_def symb.p (symb.c,symb.c) params ret t_expr

let translate_command acc command =
  match command.c with
  | Cmd_Assert(assert_term) ->
    (translate_assert assert_term) :: acc
  | Cmd_CheckEntailment(assert_term) ->
    Options.set_unsat_mode false;
    (translate_goal assert_term) :: acc
  | Cmd_CheckSat ->
    Options.set_unsat_mode true;
    (mk_goal command.p "g" (mk_false_const command.p)) :: acc
  | Cmd_CheckSatAssum prop_lit_list  ->
    Options.set_unsat_mode true;
    assert false
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
  | Cmd_Echo(attribute_value) -> acc
  | Cmd_GetAssert -> acc
  | Cmd_GetProof -> acc
  | Cmd_GetUnsatCore -> acc
  | Cmd_GetValue(term_list) -> acc
  | Cmd_GetAssign -> acc
  | Cmd_GetOption(keyword) -> acc
  | Cmd_GetInfo(key_info) -> acc
  | Cmd_GetModel -> acc
  | Cmd_GetUnsatAssumptions -> acc
  | Cmd_Reset -> acc
  | Cmd_ResetAssert -> acc
  | Cmd_SetLogic(symbol) -> acc
  | Cmd_SetOption(option) -> acc
  | Cmd_SetInfo(attribute) -> acc
  | Cmd_Push(string) -> acc
  | Cmd_Pop(string) -> acc
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

let file_parser commands =
  Smtlib_typing.typing commands;

  if Options.type_smt2 () then
    []
  else begin
    let l = List.fold_left translate_command [] (List.rev commands) in
    (init ()) @ l
  end

let lexpr_parser l = assert false
let trigger_parser t = assert false
