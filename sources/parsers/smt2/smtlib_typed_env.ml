open Smtlib_error
module SMap = Map.Make(String)

let init len f =
  let rec init_aux i n f =
    if i >= n then []
    else
      let r = f i in
      r :: init_aux (i+1) n f
  in init_aux 0 len f

type assoc =
  | Right
  | Left
  | Chainable
  | Pairwise

type fun_def = {
  params : Smtlib_ty.ty;
  assoc : assoc option;
}

type env = {
  sorts : ((int * int) *
           (string ->
            (Smtlib_ty.ty list * int list) -> Smtlib_ty.desc)) SMap.t;
  funs : fun_def list SMap.t;
}

let empty () = {
  sorts = SMap.empty;
  funs = SMap.empty;
}

(******************************************************************************)
(*********************************** Printer **********************************)
let print_sort s (arit_s, arit_t) =
  Printf.printf "%s : %d / %d \n%!" s arit_s arit_t

let print_fun s fun_def =
  Printf.printf "%s : %s \n%!" s (Smtlib_ty.to_string fun_def.params)

let print_env env =
  SMap.iter (fun s (arit, _) ->
      print_sort s arit
    ) env.sorts;
  SMap.iter (fun s fun_defs ->
      List.iter (fun fun_def ->
          print_fun s fun_def
        ) fun_defs
    ) env.funs

open Smtlib_syntax
(******************************************************************************)
(*********************************** Utils ************************************)

let get_arit symb arit =
  try int_of_string arit
  with  _ ->
    error (Typing_error "This expression is not an int") symb.Smtlib_syntax.p

let get_index i =
  match i.c with
  | IndexSymbol(symb) -> symb.c
  | IndexNumeral(s) -> s

let get_identifier id =
  match id.c with
  | IdSymbol(symb) -> symb
  | IdUnderscoreSymNum(symb,index_list) ->
    { symb with c = List.fold_left (fun s i ->
          Printf.sprintf "%s %s" s (get_index i)
        ) symb.c index_list}

let check_identifier id arit =
match id.c with
  | IdSymbol(symb) -> assert (arit = 0);
  | IdUnderscoreSymNum(symb,index_list) ->
    assert (List.length index_list = arit)

(******************************************************************************)
(*********************************** Sorts ************************************)
let check_sort_already_exist (env,locals) symb =
  if SMap.mem symb.c locals then
    error (Sort_declaration_error
             ("sort " ^ symb.c ^ " already declared/defined")) symb.p
  else if SMap.mem symb.c env.sorts then
    error (Sort_declaration_error
             ("sort " ^ symb.c ^ " already declared/defined")) symb.p

let check_sort_exist (env,locals) symb =
  if not (SMap.mem symb.c locals) then
    if not (SMap.mem symb.c env.sorts) then
      error (Sort_declaration_error
               ("sort " ^ symb.c ^ " undeclared/undefined")) symb.p

let mk_sort_definition arit_s arit_t is_dt =
  if is_dt then
    ((arit_s,arit_t),(fun s (l,_) ->
         assert (List.length l = arit_s); Smtlib_ty.TDatatype(s,l)))
  else
    ((arit_s,arit_t),(fun s (l,_) ->
         assert (List.length l =  arit_s); Smtlib_ty.TSort(s,l)))

let mk_sort (env,locals) symb sort_def =
  check_sort_already_exist (env,locals) symb;
  {env with sorts = SMap.add symb.c sort_def env.sorts}

let mk_sort_decl (env,locals) symb arit is_dt =
  let arit = get_arit symb arit in
  let sort_def = mk_sort_definition arit 0 is_dt in
  mk_sort (env,locals) symb sort_def

let find_sort_def env symb =
  try SMap.find symb.c env.sorts
  with Not_found ->
    error (Sort_declaration_error ("Undefined sort " ^ symb.c)) symb.p

let add_sorts env sorts =
  List.fold_left (fun env (name,sort) ->
      {env with sorts = SMap.add name sort env.sorts}
    ) env sorts

let rec find_sort_symb (env,locals) symb pars =
  try SMap.find symb.c locals
  with Not_found ->
    let (arit_s,arit_t),fun_sort = find_sort_def env symb in
    assert (List.length pars = arit_s);
    Smtlib_ty.new_type (fun_sort symb.c (pars,[]))

and find_sort (env,locals) sort =
  match sort.c with
    | SortIdentifier id ->
      let symb = get_identifier id in
      find_sort_symb (env,locals) symb []
    | SortIdMulti (id, sort_list) ->
      let symb = get_identifier id in
      let arg_sort = List.map (fun s ->
          find_sort (env,locals) s
        ) sort_list in
      find_sort_symb (env,locals) symb arg_sort

(******************************************************************************)
(************************************ Funs ************************************)
let extract_arit_ty_assoc ty =
  match ty.Smtlib_ty.desc with
  | Smtlib_ty.TFun(params,_) ->
    List.length params,
    (try List.hd params with _ -> Smtlib_ty.new_type (Smtlib_ty.TDummy))
  | _ -> assert false

let rec compare_fun_assoc (env,locals) symb ty f assoc =
  let arit,t_fun = extract_arit_ty_assoc ty in
  let _,t_fun = Smtlib_ty.inst locals Smtlib_ty.IMap.empty t_fun in
  let params = init arit (fun i -> t_fun) in
  let ret =
    match assoc with
    | Right | Left -> t_fun
    | Chainable | Pairwise -> Smtlib_ty.new_type (Smtlib_ty.TBool)
  in
  let def = Smtlib_ty.new_type (Smtlib_ty.TFun (params,ret)) in
  let _,def = Smtlib_ty.inst SMap.empty Smtlib_ty.IMap.empty def in
  Smtlib_ty.unify ty def symb.p;
  Some (Smtlib_ty.fun_ret ty)

and compare_fun_def (env,locals) symb ty funs =
  let rec aux funs =
    match funs with
    | [] -> None
    | def :: funs ->
      try
        match def.assoc with
        | None ->
          let def = def.params in
          let _,def = Smtlib_ty.inst locals Smtlib_ty.IMap.empty def in
          Smtlib_ty.unify ty def symb.p;
          Some (Smtlib_ty.fun_ret ty)
        | Some a -> compare_fun_assoc (env,locals) symb ty def.params a
      with
      | _ -> aux funs
  in
  aux funs

let find_fun (env,locals) symb params =
  try
    let ty = Smtlib_ty.new_type
        (Smtlib_ty.TFun (params,Smtlib_ty.new_type Smtlib_ty.TDummy)) in
    let defs = SMap.find symb.c env.funs in
    let res = compare_fun_def (env,locals) symb ty defs in
    match res with
    | Some def -> def
    | None ->
      error (Typing_error (Printf.sprintf "Undefined fun definition %s : %s"
                             symb.c (Smtlib_ty.to_string ty))) symb.p
  with Not_found -> error (Typing_error ("Undefined fun : " ^ symb.c)) symb.p

let check_fun_exists (env,locals) symb params =
  try
    let ty = Smtlib_ty.new_type
        (Smtlib_ty.TFun (params,Smtlib_ty.new_type Smtlib_ty.TDummy)) in
    let defs = SMap.find symb.c env.funs in
    let res = compare_fun_def (env,locals) symb ty defs in
    match res with
    | Some _ ->
      error (Fun_declaration_error
               ("Function already declared/defined : " ^ symb.c)) symb.p
    | None -> ()
  with Not_found -> ()

let mk_fun_ty pars ret assoc =
  let ty = Smtlib_ty.new_type (Smtlib_ty.TFun(pars,ret)) in
  {params= ty; assoc = assoc}

let add_fun_def (env,locals) ?(init=false) name params return assoc =
  if not init then check_fun_exists (env,locals) name params;
  let funs =
    try SMap.find name.c env.funs
    with Not_found -> []
  in
  {env with funs = SMap.add name.c
                ((mk_fun_ty params return assoc) :: funs) env.funs}

let mk_fun_dec (env,locals) (name,pars,return) =
  let pars = List.map (fun par ->
      let s = find_sort (env,locals) par in
      Smtlib_ty.unify par.ty s par.p;
      s
    ) pars in
  let s_return = find_sort (env,locals) return in
  Smtlib_ty.unify return.ty s_return return.p;
  add_fun_def (env,locals) name pars s_return

let mk_fun_def (env,locals) (name,params,return) =
  let params = List.map (fun par ->
      let _,sort = par.c in
      find_sort (env,locals) sort) params in
  let return = find_sort (env,locals) return in
  add_fun_def (env,locals) name params return

let add_funs env funs c =
  List.fold_left (fun env (name,params,return,assoc) ->
        add_fun_def (env,SMap.empty) ~init:true
          {c with c=name} params return assoc
    ) env funs

let find_simpl_sort_symb (env,locals) symb params =
  let (ar_s,ar_t),fun_sort = find_sort_def env symb in
  assert (ar_s = (SMap.cardinal params));
  Smtlib_ty.new_type (fun_sort symb.c
                        ((SMap.fold (fun s t l -> t :: l ) params []),[]))

(******************************************************************************)
(*********************************** Datatypes ********************************)
let extract_pars locals pars =
  let pars = List.fold_left (fun pars par ->
      let symb = par.c in
      if SMap.mem symb pars then
        error (Typing_error ("Type variable already declared : " ^ symb)) par.p;
      let ty = Smtlib_ty.new_type (Smtlib_ty.TVar(symb)) in
      Smtlib_ty.unify par.ty ty par.p;
      SMap.add symb ty pars
    ) SMap.empty pars; in
  SMap.union (fun k v1 v2 -> Some v2) locals pars

let mk_const (env,locals) (name,const_dec) =
  match const_dec.c with
  | Const_dec_sort(sort) ->
    mk_fun_dec (env,locals) (name,[],sort) None
  | Const_dec_par(pars,sort) ->
    let locals = extract_pars locals pars in
    mk_fun_dec (env,locals) (name,[],sort) None

let mk_fun_def (env,locals) (name,params,return) =
  mk_fun_dec (env,locals) (name,params,return) None

let mk_fun_dec (env,locals) (name,fun_dec) =
  match fun_dec.c with
  | Fun_dec(params,return) -> mk_fun_dec (env,locals) (name,params,return) None
  | Fun_dec_par(pars,params,return) ->
    let locals = extract_pars locals pars in
    mk_fun_dec (env,locals) (name,params,return) None

let find_sort_name sort =
  match sort.c with
  | SortIdentifier id -> get_identifier id
  | SortIdMulti (id, _) -> get_identifier id

let mk_sort_def (env,locals) symb pars sort =
  let locals_old = locals in
  let locals = extract_pars locals pars in
  let pars = List.map (fun par -> SMap.find par.c locals) pars in
  let sort =  find_sort (env,locals) sort in
  let arit = List.length pars in
  let sort_def = (arit,0), (fun s (l,_) ->
      assert (List.length l = arit);
      let links = List.fold_left2 (fun links t1 t2 ->
          let links, t2 = Smtlib_ty.inst locals_old links t2 in
          Smtlib_ty.unify t1 t2 symb.p;
          links
        ) (Smtlib_ty.IMap.empty) l pars
      in
      let sort = Smtlib_ty.subst links sort in
      sort.Smtlib_ty.desc
    )
  in
  {env with sorts = SMap.add symb.c sort_def env.sorts}

(******************************************************************************)
(*********************************** Datatypes ********************************)
let find_constr env symb =
  try
    let cstrs = SMap.find symb.c env.funs in
    if (List.length cstrs > 1) then
      error (Typing_error
               ("Constructor have mutliple signatures : " ^ symb.c)) symb.p;
    (try (List.hd cstrs).params with e ->
       error (Typing_error ("Undefined Constructor : " ^ symb.c)) symb.p;)
  with Not_found ->
    error (Typing_error ("Undefined Constructor : " ^ symb.c)) symb.p

let mk_constr_decs (env,locals) dt dt_sort constr_decs =
  let env = List.fold_left (fun env (symb_cstr,selector_dec_list) ->
      let env,destr_list =
        (* Add all destructors *)
        List.fold_left (fun (env,destr_list) (symb_destr,sort_destr) ->
            let return = find_sort (env,locals) sort_destr in
            let env, l =
              add_fun_def (env,locals) symb_destr [dt_sort] return None,
              return :: destr_list in
            env, l
          ) (env,[]) selector_dec_list in
      let env =
        add_fun_def (env,locals) symb_cstr (List.rev destr_list) dt_sort None in

      (* tester of constructor *)
      let is_cstr = { symb_cstr with c = Printf.sprintf "is %s" symb_cstr.c } in
      let env = add_fun_def (env,locals) is_cstr
          [(Smtlib_ty.new_type (Smtlib_ty.TDatatype("",[])))]
          (Smtlib_ty.new_type Smtlib_ty.TBool) None in
      env
    ) env constr_decs
  in
  env

let mk_dt_dec (env,locals) dt dt_dec =
  match dt_dec.c with
  | Datatype_dec_constr(constructor_dec_list) ->
    let dt_sort = find_simpl_sort_symb (env,locals) dt SMap.empty in
    mk_constr_decs (env,locals) dt dt_sort constructor_dec_list
  | Datatype_dec_par((symbol_list), (constructor_dec_list)) ->
    let dt_pars =
      List.fold_left (fun pars s ->
          let a = Smtlib_ty.new_type (Smtlib_ty.TVar s.c) in
          SMap.add s.c a pars
        ) SMap.empty symbol_list in
    let locals = SMap.union (fun k v1 v2 -> Some v2) locals dt_pars in
    let dt_sort = find_simpl_sort_symb (env,locals) dt dt_pars in
    mk_constr_decs (env,locals) dt dt_sort constructor_dec_list

let mk_datatype (env,locals) dt dt_dec =
  let arit =
    match dt_dec.c with
    | Datatype_dec_constr _ -> 0
    | Datatype_dec_par((symbol_list), _) ->
      List.length symbol_list
  in
  let sort_def = mk_sort_definition arit 0 true in
  let env = mk_sort (env,locals) dt sort_def in
  mk_dt_dec (env,locals) dt dt_dec

let mk_datatypes (env,locals) sort_decs datatype_decs =
  let env = List.fold_left (fun env (symb,arit) ->
      mk_sort_decl (env,locals) symb arit true
    ) env sort_decs in
  let env = List.fold_left2 (fun env (symb, arit) dt_dec ->
      mk_dt_dec (env,locals) symb dt_dec
    ) env sort_decs datatype_decs in
  env
