open Smtlib_error
open Smtlib_syntax
open Smtlib_typed_env

let assert_mode = false
let print_mode = false

(*********************************** Printers *********************************)
let print_cst cst =
  let cst,ty =
    match cst with
  | Const_Dec (s) -> s,"Real"
  | Const_Num (s) -> s,"Int"
  | Const_Str (s) -> s,"String"
  | Const_Hex (s) -> s,"Int"
  | Const_Bin (s) -> s,"Int"
  in
  Printf.printf "(%s:%s)" cst ty

let print_qualidentifier q =
  match q.c with
  | QualIdentifierId (id) ->
    let symb = get_identifier id in
    Printf.printf "(%s(%d):%s)"
      symb.c symb.ty.Smtlib_ty.id (Smtlib_ty.to_string q.ty)
  | QualIdentifierAs (id, sort) ->
    let symb = get_identifier id in
    Printf.printf "(%s(%d):%s)"
      symb.c symb.ty.Smtlib_ty.id (Smtlib_ty.to_string q.ty)

let rec print_term t =
  match t with
  | TermSpecConst (cst) ->
    print_cst cst
  | TermQualIdentifier (qualid) ->
    print_qualidentifier qualid
  | TermQualIdTerm (qualid,term_list) ->
    Printf.printf " (";
    print_qualidentifier qualid;
    List.iter (fun t -> print_term t.c) term_list;
    Printf.printf ") ";
  | TermForAllTerm (sorted_var_list, term) -> ()
  | _ -> assert false

let print_term t =
  print_term t;
  Printf.printf "\n%!"

(******************************************************************************)
let inst_and_unify (env,locals) m a b pos =
  let m, a = Smtlib_ty.inst locals m a in
  Smtlib_ty.unify a b pos

let find_par_ty (env,locals) symb pars =
  let ty = try
      let res = SMap.find symb.c locals in
      symb.is_quantif <- true;
      res
    with Not_found -> find_fun (env,locals) symb pars
  in
  ty

let check_if_dummy t l =
  if Smtlib_ty.is_dummy t.ty then
    t :: l
  else
    l

let check_if_escaped l =
  List.iter (fun d ->
      if Smtlib_ty.is_dummy d.ty then begin
        error (Typing_error ("Escaped type variables")) d.p;
      end;
    ) l

let type_cst c =
  match c with
  | Const_Dec (s) -> Smtlib_ty.new_type Smtlib_ty.TReal
  | Const_Num (s) ->
    Smtlib_ty.new_type
      (if get_is_real () then Smtlib_ty.TReal else Smtlib_ty.TInt)
  | Const_Str (s) -> Smtlib_ty.new_type Smtlib_ty.TString
  | Const_Hex (s) ->
    Smtlib_ty.new_type
      (if get_is_real () then Smtlib_ty.TReal else Smtlib_ty.TInt)
  | Const_Bin (s) ->
    Smtlib_ty.new_type
      (if get_is_real () then Smtlib_ty.TReal else Smtlib_ty.TInt)

let type_qualidentifier (env,locals) q pars =
  match q.c with
  | QualIdentifierId (id) ->
    let symb = get_identifier id in
    let ty = find_par_ty (env,locals) symb pars in
    inst_and_unify (env,locals) Smtlib_ty.IMap.empty ty q.ty q.p;
    ty
  | QualIdentifierAs (id, sort) ->
    let symb = get_identifier id in
    let ty = find_par_ty (env,locals) symb pars in
    let ty_sort = find_sort (env,locals) sort in
    inst_and_unify (env,locals) Smtlib_ty.IMap.empty ty ty_sort symb.p;
    Smtlib_ty.unify sort.ty ty_sort sort.p;
    Smtlib_ty.unify q.ty ty q.p;
    ty

let type_pattern (env,locals) ty pat =
  match pat.c with
  | PatternSymb (symb) ->
    let ty = Smtlib_ty.new_type (Smtlib_ty.TFun ([],ty)) in
    let cst_def = find_constr env symb in
    inst_and_unify (env,locals) Smtlib_ty.IMap.empty ty cst_def symb.p;
    SMap.empty
  | PatternSymbplus (symb, pars) ->
    let locals,pars = List.fold_left (fun (locals,pars) par ->
        let ty = (Smtlib_ty.new_type (Smtlib_ty.TVar(par.c))) in
        SMap.add par.c ty locals, ty :: pars
      ) (locals,[]) (List.rev pars) in
    let ty = Smtlib_ty.new_type (Smtlib_ty.TFun (pars,ty)) in
    let cst_def = find_constr env symb in
    inst_and_unify (env,locals) Smtlib_ty.IMap.empty ty cst_def symb.p;
    locals

let rec type_match_case (env,locals,dums) ty (pattern,term) =
  let pars = type_pattern (env,locals) ty pattern in
  (* shadowing *)
  let locals = SMap.union (fun k v1 v2 -> Some v2) locals pars in
  type_term (env,locals,dums) term

and type_key_term (env,locals,dums) key_term =
  match key_term.c with
  | Pattern(term_list) ->
    List.fold_left (fun dums t ->
        let _,dums = type_term (env,locals,dums) t in
        dums
      ) [] term_list
  | Named(symb) ->
    if Options.verbose () then
      Printf.eprintf "[Warning] (! :named not yet supported)\n%!";
    dums

and type_term (env,locals,dums) t =
  if print_mode then
    print_term t.c;
  match t.c with
  | TermSpecConst (cst) ->
    Smtlib_ty.unify t.ty (type_cst cst) t.p;
    t.ty, dums

  | TermQualIdentifier (qualid) ->
    let ty_q = type_qualidentifier (env,locals) qualid [] in
    Smtlib_ty.unify t.ty ty_q t.p;
    t.ty, check_if_dummy t dums

  | TermQualIdTerm (qualid,term_list) ->
    let pars,dums =
        List.fold_left (fun (pars,dums) t ->
          let ty, dums = type_term (env,locals,dums) t in
          ty :: pars, dums
          ) ([],dums) term_list in
    let pars = List.rev pars in
    let q = (type_qualidentifier (env,locals) qualid pars) in
    Smtlib_ty.unify t.ty q t.p;
    t.ty, check_if_dummy t dums

  | TermLetTerm (varbinding_list,term) ->
    let locals,dums = List.fold_left (fun (locals,dums) var_bind ->
        let symb,term = var_bind.c in
        let ty, dums = type_term (env,locals,dums) term in
        SMap.add symb.c ty locals, dums
      ) (locals,dums) varbinding_list in
    let ty,dums = type_term (env,locals,dums) term in
    Smtlib_ty.unify t.ty ty t.p;
    t.ty, dums

  | TermForAllTerm (sorted_var_list, term) ->
    let locals = List.fold_left (fun locals sorted ->
        let symb,sort = sorted.c in
        SMap.add symb.c (find_sort (env,locals) sort) locals
      ) locals sorted_var_list in
    let ty,dums = type_term (env,locals,dums) term in
    Smtlib_ty.unify t.ty ty t.p;
    t.ty, dums

  | TermExistsTerm (sorted_var_list, term) ->
    let locals = List.fold_left (fun locals sorted ->
        let symb,sort = sorted.c in
        SMap.add symb.c (find_sort (env,locals) sort) locals
      ) locals sorted_var_list in
    let ty,dums = type_term (env,locals,dums) term in
    Smtlib_ty.unify t.ty ty t.p;
    t.ty, dums

  | TermExclimationPt (term, key_term_list) ->
    let dums = List.fold_left (fun dums kt ->
        type_key_term (env,locals,dums) kt
      ) dums key_term_list in
    let ty,dums = type_term (env,locals,dums) term in
    if Options.verbose () then
      Printf.eprintf ":named not yet implemented\n%!";
    ty, dums

  | TermMatch (term, match_case_list) ->
    let ty,dums = type_term (env,locals,dums) term in
    (* check if term is datatype *)
    Smtlib_ty.unify (Smtlib_ty.new_type (Smtlib_ty.TDatatype("",[]))) ty term.p;
    let res,dums = List.fold_left (fun (res,dums) mc ->
        let ty_mc, dums = type_match_case (env,locals,dums) ty mc in
        Smtlib_ty.unify res ty_mc term.p;
        res,dums
      ) ((Smtlib_ty.new_type (Smtlib_ty.TVar "A")),dums) match_case_list in
    res,dums

let get_term (env,locals) term =
  match term.c with
  | Assert_dec t ->
    print_term t.c;
    let ty,dums = type_term (env,locals,[]) t in
    check_if_escaped dums;
    ty
  | Assert_dec_par (pars,t) ->
    let locals = Smtlib_typed_env.extract_pars locals pars in
    let ty,dums = type_term (env,locals,[]) t in
    check_if_escaped dums;
    ty

let get_sorted_locals (env,locals) params =
  List.fold_left (fun locals param ->
      let symb,sort = param.c in
      SMap.add symb.c (Smtlib_typed_env.find_sort (env,locals) sort) locals
    ) locals (List.rev params)

let get_fun_def_locals (env,locals) fun_def =
  match fun_def.c with
  | Fun_def(name,params,return) ->
    let locals = get_sorted_locals (env,locals) params in
    let ret = (Smtlib_typed_env.find_sort (env,locals) return) in
    let params = List.map (fun param -> let _,sort = param.c in sort) params in
    locals, ret, (name,params,return)
  | Fun_def_par(name,pars,params,return) ->
    let locals = Smtlib_typed_env.extract_pars locals pars in
    let locals = get_sorted_locals (env,locals) params in
    let ret = (Smtlib_typed_env.find_sort (env,locals) return) in
    let params = List.map (fun param -> let _,sort = param.c in sort) params in
    locals, ret, (name,params,return)

(******************************************************************************)
(************************************ Commands ********************************)
let type_command (env,locals) c =
  match c.c with
  | Cmd_Assert(term) | Cmd_CheckEntailment(term) ->
    Smtlib_ty.unify
      (Smtlib_ty.new_type Smtlib_ty.TBool) (get_term (env,locals) term) term.p;
    env
  | Cmd_CheckSat ->
    if assert_mode then assert false; env
  | Cmd_CheckSatAssum prop_lit ->
    if assert_mode then assert false; env
  | Cmd_DeclareConst (symbol,const_dec) ->
    Smtlib_typed_env.mk_const (env,locals) (symbol,const_dec)
  | Cmd_DeclareDataType (symbol,datatype_dec) ->
    Smtlib_typed_env.mk_datatype (env,locals) symbol datatype_dec
  | Cmd_DeclareDataTypes (sort_dec_list, datatype_dec_list) ->
    Smtlib_typed_env.mk_datatypes (env,locals) sort_dec_list datatype_dec_list
  | Cmd_DeclareFun (name,fun_dec) ->
    Smtlib_typed_env.mk_fun_dec (env,locals) (name,fun_dec)
  | Cmd_DeclareSort (symbol,arit) ->
    Smtlib_typed_env.mk_sort_decl (env,locals) symbol arit false
  | Cmd_DefineFun (fun_def,term) ->
    let locals,ret,fun_dec = get_fun_def_locals (env,locals) fun_def in
    let ty,dums = type_term (env,locals,[]) term in
    check_if_escaped dums;
    let env = Smtlib_typed_env.mk_fun_def (env,locals) fun_dec in
    inst_and_unify (env,locals) Smtlib_ty.IMap.empty ret ty term.p;
    env
  | Cmd_DefineFunRec (fun_def,term) ->
    let locals,ret,fun_dec = get_fun_def_locals (env,locals) fun_def in
    let env = Smtlib_typed_env.mk_fun_def (env,locals) fun_dec in
    let ty,dums = type_term (env,locals,[]) term in
    check_if_escaped dums;
    inst_and_unify (env,locals) Smtlib_ty.IMap.empty ret ty term.p;
    env
  | Cmd_DefineFunsRec (fun_def_list, term_list) ->
    let env,locals_term_list =
      List.fold_left (fun (env,locals_term_list) fun_def ->
          let locals,ret,fun_dec = get_fun_def_locals (env,locals) fun_def in
          let env = Smtlib_typed_env.mk_fun_def (env,locals) fun_dec in
          env, (locals,ret) :: locals_term_list
      ) (env,[]) (List.rev fun_def_list)
    in
    List.iter2 (fun (locals,ret) term ->
        let ty,dums = type_term (env,locals,[]) term in
        check_if_escaped dums;
        inst_and_unify (env,locals) Smtlib_ty.IMap.empty ret ty term.p;
      ) locals_term_list term_list;
    env
  | Cmd_DefineSort (symbol, symbol_list, sort) ->
    Smtlib_typed_env.mk_sort_def (env,locals) symbol symbol_list sort
  | Cmd_Echo (attribute_value) ->
    if assert_mode then assert false; env
  | Cmd_GetAssert ->
    if assert_mode then assert false; env
  | Cmd_GetProof ->
    if assert_mode then assert false; env
  | Cmd_GetUnsatCore ->
    if assert_mode then assert false; env
  | Cmd_GetValue (term_list) ->
    if assert_mode then assert false; env
  | Cmd_GetAssign ->
    if assert_mode then assert false; env
  | Cmd_GetOption (keyword) ->
    if assert_mode then assert false; env
  | Cmd_GetInfo (key_info) ->
    if assert_mode then assert false; env
  | Cmd_GetModel ->
    if assert_mode then assert false; env
  | Cmd_GetUnsatAssumptions ->
    if assert_mode then assert false; env
  | Cmd_Reset ->
    if assert_mode then assert false; env
  | Cmd_ResetAssert ->
    if assert_mode then assert false; env
  | Cmd_SetLogic(symb) ->
    Smtlib_typed_logic.set_logic env symb
  | Cmd_SetOption (option) ->
    if assert_mode then assert false; env
  | Cmd_SetInfo (attribute) ->
    if assert_mode then assert false; env
  | Cmd_Push _ | Cmd_Pop _ ->
    error (Incremental_error ("incremental command not suported")) c.p
  | Cmd_Exit -> env

let typing parsed_ast =
  let env =
    if not (get_logic ()) then
      try
        let c = List.hd parsed_ast in
        Smtlib_typed_logic.set_logic
          (Smtlib_typed_env.empty ()) {c with c="ALL"}
      with _ -> assert false
    else Smtlib_typed_env.empty ()
  in
  let env =
    List.fold_left (fun env c ->
        type_command (env,SMap.empty)  c
      ) env parsed_ast
  in if false then begin
    Smtlib_printer.print parsed_ast;
    Smtlib_typed_env.print_env env;
  end
