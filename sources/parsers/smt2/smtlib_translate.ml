open Options
open Parsed_interface
open Smtlib_syntax

(******************************************************************************)
let translate_left_assoc f id params =
  let rec aux acc params =
    match params with
    | [] -> acc
    | t :: tl ->
      aux (f id.p acc t) tl
  in
  if params == [] then
    assert false
  else
    aux (List.hd params) params

let translate_right_assoc f id params =
  let rec aux acc params =
    match params with
    | [] -> acc
    | t :: tl ->
      aux (f id.p t acc) tl
  in
  if params == [] then
    assert false
  else
    aux (List.hd params) params

let rec translate_chainable_assoc f id params =
  match params with
  | [] -> assert false
  | [t] -> t
  | [t1;t2] -> f id.p t1 t2
  | t1 :: ((t2 :: _) as tl) ->
    let eq = f id.p t1 t2 in
    mk_and id.p eq (translate_chainable_assoc f id tl)

(******************************************************************************)

let init n f =
  let rec init_aux i n f =
    if i >= n then []
    else
      let r = f i in
      r :: init_aux (i+1) n f
  in
  init_aux 0 n f

let get_sort_symb s pars =
  match s.c with
  | "Int" -> int_type
  | "Bool" -> bool_type
  | "Real" -> real_type
  | _ ->
    if List.mem s pars then
      mk_var_type s.p s.c
    else
      mk_external_type s.p [] s.c

let get_sort_id id pars =
  match id.c with
  | IdSymbol s -> get_sort_symb s pars
  | IdUnderscoreSymNum (s,index_list) -> assert false

let rec get_sort pars s =
  match s.c with
  | SortIdentifier s -> get_sort_id s pars
  | SortIdMulti(id,sl) ->
    let id = Smtlib_typed_env.get_identifier id in
    mk_external_type s.p (List.map (get_sort pars) sl) id.c

let translate_constant cst loc =
  match cst with
  | Const_Dec(s) -> mk_real_const loc (Num.num_of_string s)
  | Const_Num(s) -> mk_int_const loc s
  | Const_Str(s) -> assert false (* to do *)
  | Const_Hex(s) -> mk_int_const loc s
  | Const_Bin(s) -> mk_int_const loc s

let translate_identifier id params raw_params =
  let name = Smtlib_typed_env.get_identifier id in
  match name.c with
  | "true" -> mk_true_const name.p
  | "false" -> mk_false_const name.p
  | "+" -> translate_left_assoc mk_add name params
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
    let res = List.for_all (fun par ->
        let _, ty = Smtlib_ty.inst Smtlib_typed_env.SMap.empty Smtlib_ty.IMap.empty par.ty in
        try Smtlib_ty.unify (Smtlib_ty.new_type Smtlib_ty.TBool) ty name.p;
          true
        with _ -> false
      ) raw_params
    in
    if res then
      translate_chainable_assoc mk_iff name params
    else
      translate_chainable_assoc mk_pred_eq name params
  | "=>" -> translate_right_assoc mk_implies name params
  | "and" -> translate_left_assoc mk_and name params
  | "or" -> translate_left_assoc mk_or name params
  | "ite" -> begin
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

let translate_qual_identifier qid params =
  match qid.c with
  | QualIdentifierId(id) -> translate_identifier id params
  | QualIdentifierAs(id,sort) -> translate_identifier id params (* to check *)

let rec translate_term pars term =
  match term.c with
  | TermSpecConst(cst) -> translate_constant cst term.p
  | TermQualIdentifier(qid) -> translate_qual_identifier qid [] []
  | TermQualIdTerm(qid,term_list) ->
    let params = List.map (translate_term pars) term_list in
    translate_qual_identifier qid params term_list
  | TermLetTerm(varbinding_list,term) ->
    List.fold_left (fun t varbinding ->
        let s,term = varbinding.c in
        mk_let s.p s.c (translate_term pars term) t
      ) (translate_term pars term) (List.rev varbinding_list)
  | TermForAllTerm(sorted_var_list,t) ->
    let svl = List.map (fun sv ->
        let v,s = sv.c in
        v.c, "", get_sort pars s
      ) sorted_var_list in
    mk_forall term.p svl [] [] (translate_term pars t)
  | TermExistsTerm(sorted_var_list,term) ->
    let svl = List.map (fun sv ->
        let v,s = sv.c in
        v.c, "", get_sort pars s
      ) sorted_var_list in
    mk_exists term.p svl [] [] (translate_term pars term)
  | TermExclimationPt(term,key_term_list) ->
    Printf.eprintf "[Warning] (! :pattern and :named not yet supported)\n%!";
    translate_term pars term
  | TermMatch(term,pattern_term_list) -> assert false

let translate_assert_term at =
  let t = match at.c with
    | Assert_dec(term) -> translate_term [] term
    | Assert_dec_par(pars,term) ->
      translate_term pars term
  in
  mk_generic_axiom at.p "a" t

(* get_sort_id s sl@pars *)

let translate_const_dec cst =
  match cst.c with
  | Const_dec_sort t -> get_sort [] t
  | Const_dec_par (pars,t) -> get_sort pars t

let translate_decl_fun f params ret =
  let logic_type = mk_logic_type params (Some ret) in
  mk_logic f.p Symbols.Other [(f.c,f.c)] logic_type

let translate_fun_dec fun_dec =
  match fun_dec.c with
  | Fun_dec (sl,s) -> List.map (get_sort []) sl, get_sort [] s
  | Fun_dec_par (pars,sl,s) ->
    List.map (get_sort pars) sl, get_sort pars s

let translate_fun_def fun_def =
  match fun_def.c with
  | Fun_def (symb,svl,sort) ->
    symb,
    List.map (fun sv -> let p,s = sv.c in p.p,p.c,get_sort [] s) svl,
    get_sort [] sort, []
  | Fun_def_par (symb,pars,svl,sort) ->
    symb,
    List.map (fun sv -> let p,s = sv.c in p.p,p.c,get_sort pars s) svl,
    get_sort pars sort,pars

let translate_fun_def fun_def term =
  let symb,params,ret,pars = translate_fun_def fun_def in
  let t_expr = translate_term pars term in
  mk_function_def symb.p (symb.c,symb.c) params ret t_expr

let translate_command acc command =
  match command.c with
  | Cmd_Assert(assert_term) ->
    (translate_assert_term assert_term) :: acc
  | Cmd_CheckSat -> (mk_goal command.p "g" (mk_false_const command.p)) :: acc
  | Cmd_CheckSatAssum prop_lit_list  -> assert false
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
  | Cmd_DefineSort(symbol,symbol_list,sort) -> assert false
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

let file_parser commands =
  Smtlib_typing.typing commands;
  Printf.printf "Smt Typing OK \n%!";

  (* Smtlib_printer.print commands; *)

  let l = List.fold_left translate_command [] (List.rev commands) in
  Printf.printf "Conversion OK \n%!";
  l

let lexpr_parser l = assert false
let trigger_parser t = assert false
