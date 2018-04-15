open Smtlib_syntax
open Smtlib_ty
open Printf

let print_ty = false

let fmt = stderr

let plop = "."

let print_constant cst =
  match cst with
  | Const_Dec s | Const_Num s | Const_Str s | Const_Hex s | Const_Bin s -> s

let print_identifier id =
  match id.c with
  | IdSymbol s -> s.c
  | IdUnderscoreSymNum _ -> assert false

let rec print_sort s =
  match s.c with
  | SortIdentifier id ->
    if true || print_ty then
      sprintf "%s:%s" (print_identifier id) (to_string s.ty)
    else
      (print_identifier id)
  | SortIdMulti (id,sl) ->
    let sl = List.map print_sort sl in
    if print_ty then
      sprintf "(%s:%s %s)" (print_identifier id) (to_string s.ty) (String.concat " " sl)
    else
      sprintf "(%s %s)" (print_identifier id) (String.concat " " sl)

let print_sorted_var (symb,sort)  =
  sprintf "(%s %s)" symb.c (print_sort sort)

let print_qualid qid =
  match qid.c with
  | QualIdentifierId(id) ->
    if print_ty then sprintf "%s:%s" (print_identifier id) (to_string qid.ty)
    else print_identifier id
  | QualIdentifierAs(id,sort) ->
    sprintf "(as %s %s)" (print_identifier id) (print_sort sort)

let rec print_var_binding (var,bind) =
  sprintf "(%s %s)" var.c (print_term bind)

and print_var_bindings varbindings =
  List.fold_left (fun acc varbinding -> sprintf "%s %s" acc (print_var_binding varbinding.c)) "" varbindings

and print_term t =
  let s =
    match t.c with
    | TermSpecConst cst -> print_constant cst
    | TermQualIdentifier qid -> print_qualid qid
    | TermQualIdTerm (qid,tl) ->
      let tl = List.map print_term tl in
      sprintf "(%s %s)" (print_qualid qid) (String.concat " " tl)
    | TermLetTerm (varbinding_list,term) ->
      sprintf "(let (%s) %s)" (print_var_bindings varbinding_list) (print_term term)
    | TermForAllTerm (sorted_vars,term) ->
      sprintf "(forall (%s) %s)" (print_sorted_vars sorted_vars) (print_term term)
    | TermExistsTerm (sorted_vars,term) ->
      sprintf "(exists (%s) %s)" (print_sorted_vars sorted_vars) (print_term term)
    | TermExclimationPt (term,key_term_list) -> (print_term term)
    | TermMatch (term,pattern_term_list) -> assert false
  in
  sprintf "%s:%s " s ((to_string t.ty))

and print_pars pars =
  List.fold_left (fun acc par -> sprintf "%s %s:%s" acc par.c (to_string par.ty)) "" pars

and print_sorts sorts =
  List.fold_left (fun acc sort -> sprintf "%s %s" acc (print_sort sort)) "" sorts

and print_sorted_vars sorted_vars =
  List.fold_left (fun acc sort -> sprintf "%s %s" acc (print_sorted_var sort.c)) "" sorted_vars



let print_assert t =
  match t.c with
  | Assert_dec(t) -> print_term t
  | Assert_dec_par(pars,t) ->
    sprintf "(par (%s) %s)" (print_pars pars) (print_term t)

let print_const_dec cst =
  match cst.c with
  | Const_dec_sort s -> print_sort s
  | Const_dec_par (pars,s) -> sprintf "(par (%s) %s)" (print_pars pars) (print_sort s)

let print_fun_dec fun_dec =
  match fun_dec.c with
  | Fun_dec (sl,s) -> sprintf "(%s) %s" (print_sorts sl) (print_sort s)
  | Fun_dec_par (pars,sl,s) -> sprintf "(par (%s) (%s) %s)" (print_pars pars) (print_sorts sl) (print_sort s)

let print_fun_def fun_def =
  match fun_def.c with
  | Fun_def (symb,svl,s) -> sprintf "%s (%s) %s" symb.c (print_sorted_vars svl) (print_sort s)
  | Fun_def_par (symb,pars,svl,s) -> sprintf "%s (par (%s) (%s) %s)" symb.c (print_pars pars) (print_sorted_vars svl) (print_sort s)

let print_command c =
  match c.c with
  | Cmd_Assert(t) ->
    printf "(assert %s)\n%!" (print_assert t)
  | Cmd_CheckSat ->
    printf "(checksat)\n%!"
  | Cmd_CheckSatAssum prop_lit_list ->
    printf "(check-sat-assuming %s)\n%!" (assert false)
  | Cmd_DeclareConst(symbol,const_dec) ->
    printf "(declare-const %s %s)\n%!" symbol.c (print_const_dec const_dec)
  | Cmd_DeclareDataType(symbol,datatype_dec) -> assert false
  | Cmd_DeclareDataTypes(sort_dec_list,datatype_dec_list) -> assert false
  | Cmd_DeclareFun(symbol,fun_dec) ->
    printf "(declare-fun %s %s)\n%!" symbol.c (print_fun_dec fun_dec)
  | Cmd_DeclareSort(symbol,s) ->
    printf "(declare-sort %s %s)\n%!" symbol.c s
  | Cmd_DefineFun(fun_def,term) ->
    printf "(define-fun %s %s)\n%!" (print_fun_def fun_def) (print_term term)
  | Cmd_DefineFunRec(fun_def,term) ->
    printf "(define-fun-rec %s %s)\n%!" (print_fun_def fun_def) (print_term term)
  | Cmd_DefineFunsRec(fun_def_list,term_list) -> assert false
  | Cmd_DefineSort(symbol,symbol_list,sort) ->
    printf "(define-sort %s (%s) %s)\n" symbol.c (print_pars symbol_list) (print_sort sort)
  | Cmd_Echo(attribute_value) -> assert false
  | Cmd_GetAssert -> assert false
  | Cmd_GetProof -> assert false
  | Cmd_GetUnsatCore -> assert false
  | Cmd_GetValue(term_list) -> assert false
  | Cmd_GetAssign -> assert false
  | Cmd_GetOption(keyword) -> assert false
  | Cmd_GetInfo(key_info) -> assert false
  | Cmd_GetModel -> assert false
  | Cmd_GetUnsatAssumptions -> assert false
  | Cmd_Reset -> assert false
  | Cmd_ResetAssert -> assert false
  | Cmd_SetLogic(symbol) -> assert false
  | Cmd_SetOption(option) -> assert false
  | Cmd_SetInfo(attribute) -> assert false
  | Cmd_Push(string) -> assert false
  | Cmd_Pop(string) -> assert false
  | Cmd_Exit -> printf "(exit)\n"

let print commands =
  List.iter print_command commands
