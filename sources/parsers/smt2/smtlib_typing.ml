open Smtlib_error
open Smtlib_syntax
open Smtlib_typed_logic
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
    Printf.printf "(%s(%d):%s)" symb.c symb.ty.id (Smtlib_ty.to_string q.ty)
  | QualIdentifierAs (id, sort) ->
    let symb = get_identifier id in
    Printf.printf "(%s(%d):%s)" symb.c symb.ty.id (Smtlib_ty.to_string q.ty)

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

let type_cst c =
  match c with
  | Const_Dec (s) -> Smtlib_ty.new_type Smtlib_ty.TReal
  | Const_Num (s) -> Smtlib_ty.new_type (if get_is_real () then Smtlib_ty.TReal else Smtlib_ty.TInt)
  | Const_Str (s) -> Smtlib_ty.new_type Smtlib_ty.TString
  | Const_Hex (s) -> Smtlib_ty.new_type (if get_is_real () then Smtlib_ty.TReal else Smtlib_ty.TInt)
  | Const_Bin (s) -> Smtlib_ty.new_type (if get_is_real () then Smtlib_ty.TReal else Smtlib_ty.TInt)

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
    let sort = find_sort (env,locals) sort in
    inst_and_unify (env,locals) Smtlib_ty.IMap.empty sort ty symb.p;
    q.ty.desc <- ty.desc;
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

let rec type_match_case (env,locals) ty (pattern,term) =
  let pars = type_pattern (env,locals) ty pattern in
  (* shadowing *)
  let locals = SMap.union (fun k v1 v2 -> Some v2) locals pars in
  type_term (env,locals) term

and type_term (env,locals) t =
  if print_mode then
    print_term t.c;
  match t.c with
  | TermSpecConst (cst) ->
    Smtlib_ty.unify t.ty (type_cst cst) t.p; t.ty

  | TermQualIdentifier (qualid) ->
    Smtlib_ty.unify t.ty (type_qualidentifier (env,locals) qualid []) t.p; t.ty

  | TermQualIdTerm (qualid,term_list) ->
    let pars =
      List.rev (
        List.fold_left (fun pars t ->
            (type_term (env,locals) t) :: pars
          ) [] term_list) in
    let q = (type_qualidentifier (env,locals) qualid pars) in
    Smtlib_ty.unify t.ty q t.p; t.ty

  | TermLetTerm (varbinding_list,term) ->
    let locals = List.fold_left (fun locals var_bind ->
        let symb,term = var_bind.c in
        SMap.add symb.c (type_term (env,locals) term) locals
      ) locals varbinding_list in
    Smtlib_ty.unify t.ty (type_term (env,locals) term) t.p; t.ty

  | TermForAllTerm (sorted_var_list, term) ->
    let locals = List.fold_left (fun locals sorted ->
        let symb,sort = sorted.c in
        SMap.add symb.c (find_sort (env,locals) sort) locals
      ) locals sorted_var_list in
    Smtlib_ty.unify t.ty (type_term (env,locals) term) t.p; t.ty

  | TermExistsTerm (sorted_var_list, term) ->
    let locals = List.fold_left (fun locals sorted ->
        let symb,sort = sorted.c in
        SMap.add symb.c (find_sort (env,locals) sort) locals
      ) locals sorted_var_list in
    Smtlib_ty.unify t.ty (type_term (env,locals) term) t.p; t.ty

  | TermExclimationPt (term, key_term_list) ->
    let ty = type_term (env,locals) term in
    if Options.verbose () then
      Printf.eprintf ":named and :pattern not yet implemented\n%!";
    ty

  | TermMatch (term, match_case_list) ->
    let ty = type_term (env,locals) term in
    (* check if term is datatype *)
    Smtlib_ty.unify (Smtlib_ty.new_type (Smtlib_ty.TDatatype("",[]))) ty term.p;
    let res = List.fold_left (fun res mc ->
        let ty_mc = type_match_case (env,locals) ty mc in
        Smtlib_ty.unify res ty_mc term.p;
        res
      ) (Smtlib_ty.new_type (Smtlib_ty.TVar "A")) match_case_list in
    res

let get_term (env,locals) term =
  match term.c with
  | Assert_dec t -> type_term (env,locals) t
  | Assert_dec_par (pars,t) ->
    let locals = Smtlib_typed_env.extract_pars locals pars in
    type_term (env,locals) t

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
  | Cmd_Assert(term) ->
    Smtlib_ty.unify (Smtlib_ty.new_type Smtlib_ty.TBool) (get_term (env,locals) term) term.p;
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
    let ty = type_term (env,locals) term in
    let env = Smtlib_typed_env.mk_fun_def (env,locals) fun_dec in
    inst_and_unify (env,locals) Smtlib_ty.IMap.empty ret ty term.p;
    env
  | Cmd_DefineFunRec (fun_def,term) ->
    let locals,ret,fun_dec = get_fun_def_locals (env,locals) fun_def in
    let env = Smtlib_typed_env.mk_fun_def (env,locals) fun_dec in
    let ty = type_term (env,locals) term in
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
        let ty = type_term (env,locals) term in
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
        Smtlib_typed_logic.set_logic (Smtlib_typed_env.empty ()) {c with c="ALL"}
      with _ -> assert false
    else Smtlib_typed_env.empty ()
  in
  let env =
    List.fold_left (fun env c ->
        type_command (env,SMap.empty)  c
      ) env parsed_ast
  in if false then
    Smtlib_typed_env.print_env env;
