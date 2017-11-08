(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Options
open Format
open Parsed
open Typed
open Errors

module S = Set.Make(String)
module Sy = Symbols.Set

module MString =
  Map.Make(struct type t = string let compare = Pervasives.compare end)

module Types = struct

  (* environment for user-defined types *)
  type t = {
    to_ty : Ty.t MString.t;
    from_labels : string MString.t; }

  let to_tyvars = ref MString.empty

  let empty =
    { to_ty = MString.empty;
      from_labels = MString.empty }

  let fresh_vars env vars loc =
    List.map
      (fun x ->
	if MString.mem x !to_tyvars then
          error (TypeDuplicateVar x) loc;
	let nv = Ty.Tvar (Ty.fresh_var ()) in
        to_tyvars := MString.add x nv !to_tyvars;
	nv
      ) vars

  let check_number_args loc lty ty =
    match ty with
      | Ty.Text (lty', s) | Ty.Trecord {Ty.args=lty'; name=s} ->
	if List.length lty <> List.length lty' then
	  error (WrongNumberofArgs (Hstring.view s)) loc;
	lty'
      | Ty.Tsum (s, _) ->
	if List.length lty <> 0 then
	  error (WrongNumberofArgs (Hstring.view s)) loc;
	[]
      | _ -> assert false

  let equal_pp_vars lpp lvars =
    try
      List.for_all2
	(fun pp x ->
	 match pp with
         | PPTvarid (y, _) -> Pervasives.(=) x y
         | _ -> false
        ) lpp lvars
    with Invalid_argument _ -> false

  let rec ty_of_pp loc env rectype = function
    | PPTint -> Ty.Tint
    | PPTbool -> Ty.Tbool
    | PPTunit -> Ty.Tunit
    | PPTreal -> Ty.Treal
    | PPTbitv n -> Ty.Tbitv n
    | PPTvarid (s, _) ->
      begin
        try MString.find s !to_tyvars
        with Not_found ->
          let nty = Ty.Tvar (Ty.fresh_var ()) in
	  to_tyvars := MString.add s nty !to_tyvars;
          nty
      end
    | PPTexternal (l, s, loc) when Pervasives.(=) s "farray" ->
      let t1,t2 = match l with
        | [t2] -> PPTint,t2
        | [t1;t2] -> t1,t2
        | _ -> error (WrongArity(s,2)) loc in
      let ty1 = ty_of_pp loc env rectype t1 in
      let ty2 = ty_of_pp loc env rectype t2 in
      Ty.Tfarray (ty1, ty2)
    | PPTexternal (l, s, loc) ->
      begin
	match rectype with
	| Some (id, vars, ty) when Pervasives.(=) s id &&
                                     equal_pp_vars l vars -> ty
	  | _ ->
	    try
	      let lty = List.map (ty_of_pp loc env rectype) l in
	      let ty = MString.find s env.to_ty in
	      let vars = check_number_args loc lty ty in
	      Ty.instantiate vars lty ty
	    with Not_found ->
	      error (UnknownType s) loc
      end

  let add env vars id body loc =
    if MString.mem id env.to_ty then error (ClashType id) loc;
    let ty_vars = fresh_vars env vars loc in
    match body with
      | Abstract ->
	{ env with to_ty = MString.add id (Ty.text ty_vars id) env.to_ty }
      | Enum lc ->
	{ env with to_ty = MString.add id (Ty.tsum id lc) env.to_ty }
      | Record lbs ->
	let lbs =
	  List.map (fun (x, pp) -> x, ty_of_pp loc env None pp) lbs in
	{ to_ty = MString.add id (Ty.trecord ty_vars id lbs) env.to_ty;
	  from_labels =
	    List.fold_left
	      (fun fl (l,_) -> MString.add l id fl) env.from_labels lbs }

  module SH = Set.Make(Hstring)

  let check_labels lbs ty loc =
    let rec check_duplicates s = function
      | [] -> ()
      | (lb, _) :: l ->
	if SH.mem lb s then error (DuplicateLabel lb) loc;
	check_duplicates (SH.add lb s) l
    in
    check_duplicates SH.empty lbs;
    match ty with
      | Ty.Trecord {Ty.lbs=l} ->
	if List.length lbs <> List.length l then
	  error WrongNumberOfLabels loc;
	List.iter
	  (fun (lb, _) ->
	    try ignore (Hstring.list_assoc lb l)
	    with Not_found -> error (WrongLabel(lb, ty)) loc) lbs;
	ty
      | _ -> assert false


  let from_labels env lbs loc =
    match lbs with
      | [] -> assert false
      | (l, _) :: _ ->
	try
	  let l = Hstring.view l in
	  let ty = MString.find (MString.find l env.from_labels) env.to_ty in
	  check_labels lbs ty loc
	with Not_found -> error (NoRecordType l) loc

  let rec monomorphized = function
    | PPTvarid (x, _) when not (MString.mem x !to_tyvars) ->
      to_tyvars := MString.add x (Ty.fresh_empty_text ()) !to_tyvars;

    | PPTexternal (args, _, _) ->
      List.iter monomorphized args

    | pp_ty -> ()

  let init_labels fl id loc = function
    | Record lbs ->
      List.fold_left
	(fun fl (s, _) ->
	  if MString.mem s fl then
	    error (ClashLabel (s, (MString.find s fl))) loc;
	  MString.add s id fl) fl lbs
    | _ -> fl

end

module Env = struct

  type profile = { args : Ty.t list; result : Ty.t }

  type t = {
    var_map : (Symbols.t * Ty.t) MString.t ; (* variables' map*)
    types : Types.t ;
    logics : (Symbols.t * profile) MString.t (* logic symbols' map *)
  }

  let empty = {
    var_map = MString.empty;
    types = Types.empty;
    logics = MString.empty
  }

  let add env lv fvar ty =
    let vmap =
      List.fold_left
	(fun vmap x -> MString.add x (fvar x, ty) vmap) env.var_map lv in
    { env with var_map = vmap }

  let add_var env lv pp_ty loc  =
    let ty = Types.ty_of_pp loc env.types None pp_ty in
    add env lv Symbols.var ty

  let add_names env lv pp_ty loc =
    Types.monomorphized pp_ty;
    let ty = Types.ty_of_pp loc env.types None pp_ty in
    add env lv Symbols.name ty

  let add_names_lbl env lv pp_ty loc =
    Types.monomorphized pp_ty;
    let ty = Types.ty_of_pp loc env.types None pp_ty in
    let rlv =
      List.fold_left (fun acc (x, lbl) ->
	let lbl = Hstring.make lbl in
	if not (Hstring.equal lbl Hstring.empty) then
	  Symbols.add_label lbl (Symbols.name x);
	x::acc
      ) [] lv in
    let lv = List.rev rlv in
    add env lv Symbols.name ty

  let add_logics env ac names pp_profile loc =
    let profile =
      match pp_profile with
	| PPredicate args ->
	  { args = List.map (Types.ty_of_pp loc env.types None) args;
	    result = Ty.Tbool }
	(*| PFunction ([], PPTvarid (_, loc)) ->
	  error CannotGeneralize loc*)
	| PFunction(args, res) ->
	  let args = List.map (Types.ty_of_pp loc env.types None) args in
	  let res = Types.ty_of_pp loc env.types None res in
	  { args = args; result = res }
    in
    let logics =
      List.fold_left
	(fun logics (n, lbl) ->
	  let sy = Symbols.name n ~kind:ac in
	  if MString.mem n logics then error (SymbAlreadyDefined n) loc;

	  let lbl = Hstring.make lbl in
	  if not (Hstring.equal lbl Hstring.empty) then
	    Symbols.add_label lbl sy;

	  MString.add n (sy, profile) logics)
	env.logics names
    in
    { env with logics = logics }

  let find {var_map=m} n = MString.find n m

  let mem n {var_map=m} = MString.mem n m

  let list_of {var_map=m} = MString.fold (fun _ c acc -> c::acc) m []

  let add_type_decl env vars id body loc =
    { env with types = Types.add env.types vars id body loc }

  (* returns a type with fresh variables *)
  let fresh_type env n loc =
    try
      let s, { args = args; result = r} = MString.find n env.logics in
      let args, subst = Ty.fresh_list args Ty.esubst in
      let res, _ = Ty.fresh r subst in
      s, { args = args; result = res }
    with Not_found -> error (SymbUndefined n) loc

end

let new_id = let r = ref 0 in fun () -> r := !r+1; !r

let rec freevars_term acc t = match t.c.tt_desc with
  | TTvar x -> Sy.add x acc
  | TTapp (_,lt) -> List.fold_left freevars_term acc lt
  | TTinInterval (e,_,_,_,_) -> freevars_term acc e
  | TTmapsTo (_, e) -> freevars_term acc e
  | TTinfix (t1,_,t2) | TTget(t1, t2) ->
    List.fold_left freevars_term acc [t1; t2]
  | TTset (t1, t2, t3) ->
    List.fold_left freevars_term acc [t1; t2; t3]
  | TTdot (t1, _) -> freevars_term acc t1
  | TTrecord lbs ->
    List.fold_left (fun acc (_, t) -> freevars_term acc t) acc lbs
  | TTconst _ -> acc
  | TTprefix (_, t) -> freevars_term acc t
  | TTconcat (t1, t2) -> freevars_term (freevars_term acc t1) t2
  | TTnamed (_, t) -> freevars_term acc t
  | TTextract (t1, t2, t3) ->
    freevars_term (freevars_term (freevars_term acc t1) t2) t3
  | TTlet (sy, t1, t2) ->
    let acc_t1 = freevars_term acc t1 in
    let acc_t2 = freevars_term acc_t1 t2 in
    if Sy.mem sy acc_t1 then acc_t2
    (* the symbol sy is already a free var in acc or t1 -> keep it *)
    else Sy.remove sy acc_t2  (* the symbol sy is not a free var *)

let freevars_atom a = match a.c with
  | TAeq lt | TAneq lt | TAle lt
  | TAlt lt | TAbuilt(_,lt) | TAdistinct lt ->
    List.fold_left freevars_term Sy.empty lt
  | TApred t -> freevars_term  Sy.empty t
  | _ -> Sy.empty

let rec freevars_form f = match f with
  | TFatom a -> freevars_atom a
  | TFop (_,lf) ->
    List.fold_left Sy.union Sy.empty
      (List.map (fun f -> freevars_form f.c) lf)
  | TFforall qf | TFexists qf ->
    let s = freevars_form qf.qf_form.c in
    List.fold_left (fun acc (s,_) -> Sy.remove s acc) s qf.qf_bvars
  | TFlet(up,v,t,f) -> freevars_term (Sy.remove v (freevars_form f.c)) t
  | TFnamed(_, f) -> freevars_form f.c

let symbol_of = function
PPadd -> Symbols.Op Symbols.Plus
  | PPsub -> Symbols.Op Symbols.Minus
  | PPmul -> Symbols.Op Symbols.Mult
  | PPdiv -> Symbols.Op Symbols.Div
  | PPmod ->  Symbols.Op Symbols.Modulo
  | _ -> assert false

let append_type msg ty =
  fprintf str_formatter "%s %a" msg Ty.print ty;
  flush_str_formatter ()

let type_var_desc env p loc =
  try
    let s,t = Env.find env p in
    Options.tool_req 1 (append_type "TR-Typing-Var$_\\Gamma$ type" t);
    TTvar s , t
  with Not_found ->
    match Env.fresh_type env p loc with
    | s, { Env.args = []; result = ty} ->
      Options.tool_req 1 (append_type "TR-Typing-Var$_\\Delta$ type" ty);
      TTvar s , ty
    | _ -> error (ShouldBeApply p) loc

let rec type_term env f =
  let e,t = type_term_desc env f.pp_loc f.pp_desc in
  {c = { tt_desc = e ; tt_ty = t }; annot = new_id ()}

and type_term_desc env loc = function
  | PPconst ConstTrue ->
    Options.tool_req 1 (append_type "TR-Typing-Const type" Ty.Tbool);
    TTconst Ttrue, Ty.Tbool
  | PPconst ConstFalse ->
    Options.tool_req 1 (append_type "TR-Typing-Const type" Ty.Tbool);
    TTconst Tfalse, Ty.Tbool
  | PPconst ConstVoid ->
    Options.tool_req 1 (append_type "TR-Typing-Const type" Ty.Tunit);
    TTconst Tvoid, Ty.Tunit
  | PPconst (ConstInt n) ->
    Options.tool_req 1 (append_type "TR-Typing-Const type" Ty.Tint);
    TTconst(Tint n), Ty.Tint
  | PPconst (ConstReal n) ->
    Options.tool_req 1 (append_type "TR-Typing-Const type" Ty.Treal);
    TTconst(Treal n), Ty.Treal
  | PPconst (ConstBitv n) ->
    Options.tool_req 1
      (append_type "TR-Typing-Const type" (Ty.Tbitv (String.length n)));
    TTconst(Tbitv n), Ty.Tbitv (String.length n)
  | PPvar p ->
    type_var_desc env p loc

  | PPapp(p,args) ->
    begin
      let te_args = List.map (type_term env) args in
      let lt_args =  List.map (fun {c={tt_ty=t}} -> t) te_args in
      let s, {Env.args = lt; result = t} = Env.fresh_type env p loc in
      try
	List.iter2 Ty.unify lt lt_args;
	Options.tool_req 1 (append_type "TR-Typing-App type" t);
	TTapp(s,te_args), t
      with
	| Ty.TypeClash(t1,t2) ->
	  error (Unification(t1,t2)) loc
	| Invalid_argument _ ->
	  error (WrongNumberofArgs p) loc
    end
  | PPinfix(t1,(PPadd | PPsub | PPmul | PPdiv as op),t2) ->
    begin
      let s = symbol_of op in
      let te1 = type_term env t1 in
      let te2 = type_term env t2 in
      let ty1 = Ty.shorten te1.c.tt_ty in
      let ty2 = Ty.shorten te2.c.tt_ty in
      match ty1, ty2 with
	| Ty.Tint, Ty.Tint ->
	  Options.tool_req 1 (append_type "TR-Typing-OpBin type" ty1);
	  TTinfix(te1,s,te2) , ty1
	| Ty.Treal, Ty.Treal ->
	  Options.tool_req 1 (append_type "TR-Typing-OpBin type" ty2);
	  TTinfix(te1,s,te2), ty2
	| Ty.Tint, _ -> error (ShouldHaveType(ty2,Ty.Tint)) t2.pp_loc
	| Ty.Treal, _ -> error (ShouldHaveType(ty2,Ty.Treal)) t2.pp_loc
	| _ -> error (ShouldHaveTypeIntorReal ty1) t1.pp_loc
    end
  | PPinfix(t1, PPmod, t2) ->
    begin
      let s = symbol_of PPmod in
      let te1 = type_term env t1 in
      let te2 = type_term env t2 in
      let ty1 = Ty.shorten te1.c.tt_ty in
      let ty2 = Ty.shorten te2.c.tt_ty in
      match ty1, ty2 with
	| Ty.Tint, Ty.Tint ->
	  Options.tool_req 1 (append_type "TR-Typing-OpMod type" ty1);
	  TTinfix(te1,s,te2) , ty1
	| _ -> error (ShouldHaveTypeInt ty1) t1.pp_loc
    end
  | PPprefix(PPneg, {pp_desc=PPconst (ConstInt n)}) ->
    Options.tool_req 1 (append_type "TR-Typing-OpUnarith type" Ty.Tint);
    TTconst(Tint ("-"^n)), Ty.Tint
  | PPprefix(PPneg, {pp_desc=PPconst (ConstReal n)}) ->
    Options.tool_req 1 (append_type "TR-Typing-OpUnarith type" Ty.Treal);
    TTconst(Treal (Num.minus_num n)), Ty.Treal
  | PPprefix(PPneg, e) ->
    let te = type_term env e in
    let ty = Ty.shorten te.c.tt_ty in
    if ty!=Ty.Tint && ty!=Ty.Treal then
      error (ShouldHaveTypeIntorReal ty) e.pp_loc;
    Options.tool_req 1 (append_type "TR-Typing-OpUnarith type" ty);
    TTprefix(Symbols.Op Symbols.Minus, te), ty
  | PPconcat(t1, t2) ->
    begin
      let te1 = type_term env t1 in
      let te2 = type_term env t2 in
      let ty1 = Ty.shorten te1.c.tt_ty in
      let ty2 = Ty.shorten te2.c.tt_ty in
      match ty1, ty2 with
	| Ty.Tbitv n , Ty.Tbitv m ->
	  Options.tool_req 1
            (append_type "TR-Typing-OpConcat type" (Ty.Tbitv (n+m)));
	  TTconcat(te1, te2), Ty.Tbitv (n+m)
	| Ty.Tbitv _ , _ -> error (ShouldHaveTypeBitv ty2) t2.pp_loc
	| _ , Ty.Tbitv _ -> error (ShouldHaveTypeBitv ty1) t1.pp_loc
	| _ -> error (ShouldHaveTypeBitv ty1) t1.pp_loc
    end
  | PPextract(e, ({pp_desc=PPconst(ConstInt i)} as ei),
	      ({pp_desc=PPconst(ConstInt j)} as ej)) ->
    begin
      let te = type_term env e in
      let tye = Ty.shorten te.c.tt_ty in
      let i = int_of_string i in
      let j = int_of_string j in
      match tye with
	| Ty.Tbitv n ->
	  if i>j then error (BitvExtract(i,j)) loc;
	  if j>=n then error (BitvExtractRange(n,j) ) loc;
	  let tei = type_term env ei in
	  let tej = type_term env ej in
          Options.tool_req 1
            (append_type "TR-Typing-OpExtract type" (Ty.Tbitv (j-i+1)));
	  TTextract(te, tei, tej), Ty.Tbitv (j-i+1)
	| _ -> error (ShouldHaveType(tye,Ty.Tbitv (j+1))) loc
    end
  | PPget (t1, t2) ->
    begin
      let te1 = type_term env t1 in
      let te2 = type_term env t2 in
      let tyarray = Ty.shorten te1.c.tt_ty in
      let tykey2 = Ty.shorten te2.c.tt_ty in
      match tyarray with
	| Ty.Tfarray (tykey,tyval) ->
	  begin
            try
	      Ty.unify tykey tykey2;
	      Options.tool_req 1 (append_type "TR-Typing-OpGet type" tyval);
              TTget(te1, te2), tyval
	    with
	      | Ty.TypeClash(t1,t2) ->
	        error (Unification(t1,t2)) loc
          end
	| _ -> error ShouldHaveTypeArray t1.pp_loc
    end
  | PPset (t1, t2, t3) ->
    begin
      let te1 = type_term env t1 in
      let te2 = type_term env t2 in
      let te3 = type_term env t3 in
      let ty1 = Ty.shorten te1.c.tt_ty in
      let tykey2 = Ty.shorten te2.c.tt_ty in
      let tyval2 = Ty.shorten te3.c.tt_ty in
      try
	match ty1 with
	  | Ty.Tfarray (tykey,tyval) ->
	    Ty.unify tykey tykey2;Ty.unify tyval tyval2;
	    Options.tool_req 1 (append_type "TR-Typing-OpSet type" ty1);
	    TTset(te1, te2, te3), ty1
	  | _ -> error ShouldHaveTypeArray t1.pp_loc
      with
	| Ty.TypeClash(t, t') ->
	  error (Unification(t, t')) loc
    end
  | PPif(t1,t2,t3) ->
    begin
      let te1 = type_term env t1 in
      let ty1 = Ty.shorten te1.c.tt_ty in
      if not (Ty.equal ty1 Ty.Tbool) then
	error (ShouldHaveType(ty1,Ty.Tbool)) t1.pp_loc;
      let te2 = type_term env t2 in
      let te3 = type_term env t3 in
      let ty2 = Ty.shorten te2.c.tt_ty in
      let ty3 = Ty.shorten te3.c.tt_ty in
      if not (Ty.equal ty2 ty3) then
	error (ShouldHaveType(ty3,ty2)) t3.pp_loc;
      Options.tool_req 1 (append_type "TR-Typing-Ite type" ty2);
      TTapp(Symbols.name "ite",[te1;te2;te3]) , ty2
    end
  | PPdot(t, a) ->
    begin
      let te = type_term env t in
      let ty = Ty.shorten te.c.tt_ty in
      match ty with
	| Ty.Trecord {Ty.name=g; lbs=lbs} ->
	  begin
	    try
	      let a = Hstring.make a in
	      TTdot(te, a), Hstring.list_assoc a lbs
	    with Not_found ->
	      let g = Hstring.view g in
	      error (ShouldHaveLabel(g,a)) t.pp_loc
	  end
	| _ -> error (ShouldHaveTypeRecord ty) t.pp_loc
    end
  | PPrecord lbs ->
    begin
      let lbs =
	List.map (fun (lb, t) -> Hstring.make lb, type_term env t) lbs in
      let lbs = List.sort
	(fun (l1, _) (l2, _) -> Hstring.compare l1 l2) lbs in
      let ty = Types.from_labels env.Env.types lbs loc in
      let ty, _ = Ty.fresh (Ty.shorten ty) Ty.esubst in
      match ty with
	| Ty.Trecord {Ty.lbs=ty_lbs} ->
	  begin
	    try
	      let lbs =
		List.map2
		  (fun (s, te) (lb,ty_lb)->
		    Ty.unify te.c.tt_ty ty_lb;
		    lb, te) lbs ty_lbs
	      in
	      TTrecord(lbs), ty
	    with Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) loc
	  end
	| _ -> error ShouldBeARecord loc
    end
  | PPwith(e, lbs) ->
    begin
      let te = type_term env e in
      let lbs =
	List.map
	  (fun (lb, t) -> Hstring.make lb, (type_term env t, t.pp_loc)) lbs in
      let ty = Ty.shorten te.c.tt_ty in
      match ty with
	| Ty.Trecord {Ty.lbs=ty_lbs} ->
	  let nlbs =
	    List.map
	      (fun (lb, ty_lb) ->
		try
		  let v, _ = Hstring.list_assoc lb lbs in
		  Ty.unify ty_lb v.c.tt_ty;
		  lb, v
		with
		  | Not_found ->
		    lb, {c = { tt_desc = TTdot(te, lb); tt_ty = ty_lb};
			 annot = te.annot }
		  | Ty.TypeClash(t1,t2) ->
		    error (Unification(t1,t2)) loc
	      ) ty_lbs
	  in
	  List.iter
	    (fun (lb, _) ->
	      try ignore (Hstring.list_assoc lb ty_lbs)
	      with Not_found -> error (NoLabelInType(lb, ty)) loc) lbs;
	  TTrecord(nlbs), ty
	| _ ->  error ShouldBeARecord loc
    end
  | PPlet(x, t1, t2) ->
    let te1 = type_term env t1 in
    let ty1 = Ty.shorten te1.c.tt_ty in
    let env = Env.add env [x] Symbols.var ty1 in
    let te2 = type_term env t2 in
    let ty2 = Ty.shorten te2.c.tt_ty in
    let s, _ = Env.find env x in
    Options.tool_req 1 (append_type "TR-Typing-Let type" ty2);
    TTlet(s, te1, te2), ty2

  (* | PPnamed(lbl, t) ->  *)
  (*     let te = type_term env t in *)
  (*     te.c.tt_desc, te.c.tt_ty *)

  | PPnamed (lbl, t) ->
    let te = type_term env t in
    let ty = Ty.shorten te.c.tt_ty in
    let lbl = Hstring.make lbl in
    TTnamed (lbl, te), ty

  | PPcast (t,ty) ->
    let ty = Types.ty_of_pp loc env.Env.types None ty in
    let te = type_term env t in
    begin try
            Ty.unify te.c.tt_ty ty;
            te.c.tt_desc, Ty.shorten te.c.tt_ty
      with
        | Ty.TypeClash(t1,t2) ->
          error (Unification(t1,t2)) loc
    end

  | _ -> error SyntaxError loc


let rec join_forall f = match f.pp_desc with
  | PPforall(vs_ty, trs1, hyp1, f) ->
    let tyvars,trs2,hyp2, f = join_forall f in
    vs_ty @ tyvars , trs1@trs2 , hyp1@hyp2, f
  | PPforall_named (named_vs_ty, trs1, hyp1, f) ->
    let vs_ty = List.map (fun (v, _, ty) -> v, ty) named_vs_ty in
    join_forall {f with pp_desc = PPforall (vs_ty, trs1, hyp1, f)}
  | PPnamed(lbl, f) ->
    join_forall f
  | _ -> [] , [] , [], f

let rec join_exists f = match f.pp_desc with
  | PPexists (vs_ty, trs1, hyp1, f) ->
    let tyvars,trs2, hyp2,f = join_exists f in
    vs_ty @ tyvars , trs1@trs2, hyp1@hyp2,  f
  | PPexists_named (named_vs_ty, trs1, hyp1, f) ->
    let vs_ty = List.map (fun (v, _, ty) -> v, ty) named_vs_ty in
    join_exists {f with pp_desc = PPexists (vs_ty, trs1, hyp1, f)}
  | PPnamed (_, f) -> join_exists f
  | _ -> [] , [] , [], f


let type_bound env bnd ty =
  try
    match bnd.pp_desc with
    | PPvar s ->
      begin
        match s.[0] with
        | '?' ->
          let res = TTvar (Symbols.Var (Hstring.make s)) in
          {c = { tt_desc = res ; tt_ty = ty }; annot = new_id ()}
        | _ -> type_term env bnd
      end
    | PPconst num ->
       begin
	 match num with
	 | ConstInt _ | ConstReal _->
	    type_term env bnd
	 | _ -> assert false
       end
    | _ -> assert false
  with Invalid_argument s when String.equal s "index out of bounds" ->
    assert false

let type_trigger in_theory env l =
  List.map
    (fun t ->
      match in_theory, t.pp_desc with
      | false, PPinInterval _ -> error ThSemTriggerError t.pp_loc
      | false, PPmapsTo _ -> error ThSemTriggerError t.pp_loc
      | true, PPinInterval (e, a,b, c, d) ->
        let te = type_term env e in
        let tt_ty = te.c.tt_ty in
        let tb = type_bound env b tt_ty in
        if not (Ty.equal tt_ty tb.c.tt_ty) then
          error (ShouldHaveType(tb.c.tt_ty,tt_ty)) b.pp_loc;

        let tc = type_bound env c tt_ty in
        if not (Ty.equal tt_ty tc.c.tt_ty) then
          error (ShouldHaveType(tc.c.tt_ty, tt_ty)) c.pp_loc;

        { c = { tt_desc = TTinInterval(te, a, tb , tc, d) ; tt_ty = Ty.Tbool};
          annot = new_id ()}

      | true, PPmapsTo (x, e) ->
        let vx, ty_x = type_var_desc env x t.pp_loc in
        let hs_x =
          match vx with TTvar Symbols.Var hs -> hs | _ -> assert false
        in
        let te = type_term env e in
        let tt_ty = te.c.tt_ty in
        if not (Ty.equal tt_ty ty_x) then
          error (ShouldHaveType(ty_x,tt_ty)) t.pp_loc;
        { c = { tt_desc = TTmapsTo(hs_x, te) ; tt_ty = Ty.Tbool};
          annot = new_id ()}

      | _ -> type_term env t
    )l

let rec type_form ?(in_theory=false) env f =
  let rec type_pp_desc pp_desc = match pp_desc with
    | PPconst ConstTrue ->
      Options.tool_req 1 "TR-Typing-True$_F$";
      TFatom {c=TAtrue; annot=new_id ()}, Sy.empty
    | PPconst ConstFalse ->
      Options.tool_req 1 "TR-Typing-False$_F$";
      TFatom {c=TAfalse; annot=new_id ()}, Sy.empty
    | PPvar p ->
      Options.tool_req 1 "TR-Typing-Var$_F$";
      let r = begin
	match Env.fresh_type env p f.pp_loc with
	  | s, { Env.args = []; result = Ty.Tbool} ->
	    let t2 = {c = {tt_desc=TTconst Ttrue;tt_ty=Ty.Tbool};
		      annot = new_id ()} in
	    let t1 = {c = {tt_desc=TTvar s; tt_ty=Ty.Tbool};
		      annot = new_id ()} in
	    TFatom {c = TAeq [t1;t2]; annot=new_id ()}
	  | _ -> error (NotAPropVar p) f.pp_loc
      end in r, freevars_form r

    | PPapp(p,args ) ->
      Options.tool_req 1 "TR-Typing-App$_F$";
      let r =
	begin
	  let te_args = List.map (type_term env) args in
	  let lt_args =  List.map (fun {c={tt_ty=t}} -> t) te_args in
	  match Env.fresh_type env p f.pp_loc with
	    | s , { Env.args = lt; result = Ty.Tbool} ->
	      begin
		try
		  List.iter2 Ty.unify lt lt_args;
		  if Pervasives.(=) p "<=" || Pervasives.(=) p "<" then
		    TFatom { c = TAbuilt(Hstring.make p,te_args);
			     annot=new_id ()}
		  else
		    let t1 = {
		      c = {tt_desc=TTapp(s,te_args); tt_ty=Ty.Tbool};
		      annot=new_id (); }
		    in
		    TFatom { c = TApred t1; annot=new_id () }
		with
		  | Ty.TypeClash(t1,t2) ->
		    error (Unification(t1,t2)) f.pp_loc
		  | Invalid_argument _ ->
		    error (WrongNumberofArgs p) f.pp_loc
	      end
	    | _ -> error (NotAPredicate p) f.pp_loc
	end
      in r, freevars_form r

    | PPdistinct (args) ->
      Options.tool_req 1 "TR-Typing-Distinct$_F$";
      let r =
	begin
	  let te_args = List.map (type_term env) args in
	  let lt_args =  List.map (fun {c={tt_ty=t}} -> t) te_args in
	  try
	    let t = match lt_args with
	      | t::_ -> t
	      | [] ->
		error (WrongNumberofArgs "distinct") f.pp_loc
	    in
	    List.iter (Ty.unify t) lt_args;
	    TFatom { c = TAdistinct te_args; annot=new_id () }
	  with
	    | Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) f.pp_loc
	end
      in r, freevars_form r

    | PPinfix
	({pp_desc = PPinfix (_, (PPlt|PPle|PPgt|PPge|PPeq|PPneq), a)} as p,
	 (PPlt | PPle | PPgt | PPge | PPeq | PPneq as r), b) ->
      Options.tool_req 1 "TR-Typing-OpComp$_F$";
	  let r =
            let q = { pp_desc = PPinfix (a, r, b); pp_loc = f.pp_loc } in
            let f1,_ = type_form env p in
            let f2,_ = type_form env q in
            TFop(OPand, [f1;f2])
	  in r, freevars_form r
    | PPinfix(t1, (PPeq | PPneq as op), t2) ->
      Options.tool_req 1 "TR-Typing-OpBin$_F$";
      let r =
	let tt1 = type_term env t1 in
	let tt2 = type_term env t2 in
	try
	  Ty.unify tt1.c.tt_ty tt2.c.tt_ty;
	  match op with
	    | PPeq -> TFatom {c = TAeq [tt1; tt2]; annot = new_id()}
	    | PPneq -> TFatom {c = TAneq [tt1; tt2]; annot = new_id()}
	    | _ -> assert false
	with Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) f.pp_loc
      in r, freevars_form r
    | PPinfix(t1, (PPlt | PPgt | PPge | PPle as op), t2) ->
      Options.tool_req 1 "TR-Typing-OpComp$_F$";
      let r =
	let tt1 = type_term env t1 in
	let tt2 = type_term env t2 in
	try
	  Ty.unify tt1.c.tt_ty tt2.c.tt_ty;
	  let ty = Ty.shorten tt1.c.tt_ty in
	  match ty with
	    | Ty.Tint | Ty.Treal ->
	      let top =
		match op with
		  | PPlt -> TAlt [tt1; tt2]
		  | PPgt -> TAlt [tt2; tt1]
		  | PPle -> TAle [tt1; tt2]
		  | PPge -> TAle [tt2; tt1]
		  | PPeq -> TAeq [tt1; tt2]
		  | PPneq -> TAneq [tt1; tt2]
		  | _ -> assert false
	      in
	      TFatom {c = top; annot=new_id ()}
	    | _ -> error (ShouldHaveTypeIntorReal ty) t1.pp_loc
	with Ty.TypeClash(t1,t2) -> error (Unification(t1,t2)) f.pp_loc
      in r, freevars_form r
    | PPinfix(f1,op ,f2) ->
      Options.tool_req 1 "TR-Typing-OpConnectors$_F$";
      begin
	let f1,fv1 = type_form env f1 in
	let f2,fv2 = type_form env f2 in
	((match op with
	  | PPand ->
	    TFop(OPand,[f1;f2])
	  | PPor -> TFop(OPor,[f1;f2])
	  | PPimplies -> TFop(OPimp,[f1;f2])
	  | PPiff -> TFop(OPiff,[f1;f2])
	  | _ -> assert false), Sy.union fv1 fv2)
      end
    | PPprefix(PPnot,f) ->
      Options.tool_req 1 "TR-Typing-OpNot$_F$";
      let f, fv = type_form env f in TFop(OPnot,[f]),fv
    | PPif(f1,f2,f3) ->
      Options.tool_req 1 "TR-Typing-Ite$_F$";
      let f1 = type_term env f1 in
      let f2,fv2 = type_form env f2 in
      let f3,fv3 = type_form env f3 in
      TFop(OPif f1,[f2;f3]), Sy.union fv2 fv3
    | PPnamed(lbl,f) ->
      let f, fv = type_form env f in
      let lbl = Hstring.make lbl in
      TFnamed(lbl, f), fv
    | PPforall _ | PPexists _ ->
      let ty_vars, triggers, hyp, f' =
	match pp_desc with
	  | PPforall(vs_ty,triggers,hyp,f') ->
	    let ty_vars, triggers', hyp', f' = join_forall f' in
	    vs_ty @ ty_vars, triggers@triggers', hyp @ hyp', f'
	  | PPexists(vs_ty,triggers,hyp,f') ->
	    let ty_vars, triggers', hyp', f' = join_exists f' in
	    vs_ty @ ty_vars, triggers@triggers', hyp @ hyp', f'
	  | _ -> assert false
      in
      let env' =
	List.fold_left
	  (fun env (v, pp_ty) ->
	    Env.add_var env [v] pp_ty f.pp_loc) env ty_vars in
      let f', fv = type_form env' f' in
      let ty_triggers =
        List.map (fun (tr, b) -> type_trigger in_theory env' tr, b) triggers in
      let qf_hyp = List.map (fun h -> fst (type_form env' h)) hyp in
      let upbvars = Env.list_of env in
      let bvars =
	List.fold_left
	  (fun acc (v,_) ->
            let ty = Env.find env' v in
            if Sy.mem (fst ty) fv then ty :: acc else acc) [] ty_vars in
      let qf_form = {
	qf_upvars = upbvars ;
	qf_bvars = bvars ;
	qf_triggers = ty_triggers ;
        qf_hyp = qf_hyp;
	qf_form = f'}
      in
      (match pp_desc with
	| PPforall _ ->
	  Options.tool_req 1 "TR-Typing-Forall$_F$";
	  TFforall qf_form
	| PPexists _ ->
	  Options.tool_req 1 "TR-Typing-Exists$_F$";
	  TFexists qf_form
	| _ -> assert false),
      (List.fold_left (fun acc (l,_) -> Sy.remove l acc) fv bvars)
    | PPlet (var,t,f) ->
      Options.tool_req 1 "TR-Typing-Let$_F$";
      let {c= { tt_ty = ttype }} as tt = type_term env t in
      let svar = Symbols.var var in
      let up = Env.list_of env in
      let env =
	{env with
	  Env.var_map = MString.add var (svar, ttype) env.Env.var_map} in
      let f,fv = type_form env f in
      TFlet (up ,svar , tt, f), freevars_term (Sy.remove svar fv) tt


    (* Remove labels : *)
    | PPforall_named (vs_tys, trs, hyp, f) ->
      let vs_tys = List.map (fun (v, _, ty) -> v, ty) vs_tys in
      type_pp_desc (PPforall (vs_tys, trs, hyp, f))
    | PPexists_named (vs_tys, trs, hyp, f) ->
      let vs_tys = List.map (fun (v, _, ty) -> v, ty) vs_tys in
      type_pp_desc (PPexists (vs_tys, trs, hyp, f))

    | PPcheck _ | PPcut _ -> assert false

    | _ ->
      let te1 = type_term env f in
      let ty = te1.c.tt_ty in
      match ty with
	| Ty.Tbool ->
	  let te2 = {c = {tt_desc=TTconst Ttrue;tt_ty=Ty.Tbool};
		     annot = new_id ()}
	  in
	  let r = TFatom {c = TAeq [te1;te2]; annot=new_id ()} in
	  r, freevars_form r
	| _ -> error ShouldHaveTypeProp f.pp_loc
  in
  let form, vars = type_pp_desc f.pp_desc in
  {c = form; annot = new_id ()}, vars


let make_rules loc f = match f.c with
  | TFforall {qf_bvars = vars; qf_form = {c = TFatom {c = TAeq [t1; t2]}}} ->
    {rwt_vars = vars; rwt_left = t1; rwt_right = t2}
  | TFatom {c = TAeq [t1; t2]} ->
    {rwt_vars = []; rwt_left = t1; rwt_right = t2}
  | _ -> error SyntaxError loc


let fresh_var =
  let cpt = ref 0 in
  fun x -> incr cpt; ("_"^x^(string_of_int !cpt))

let rec no_alpha_renaming_b ((up, m) as s) f =
  match f.pp_desc with
    | PPvar x ->
      (try
         let y = MString.find x m in
         assert (String.compare x y <> 0);
         raise Exit
       with Not_found -> ())

    | PPmapsTo(x, e) ->
      (try
         let y = MString.find x m in
         assert (String.compare x y <> 0);
         raise Exit
       with Not_found -> ());
      no_alpha_renaming_b s e

    | PPapp(k, l) ->
      List.iter (no_alpha_renaming_b s) l

    | PPinInterval(e, _,_,_,_) ->
      no_alpha_renaming_b s e

    | PPdistinct l ->
      List.iter (no_alpha_renaming_b s) l

    | PPconst _ -> ()

    | PPinfix(f1, op, f2) ->
      no_alpha_renaming_b s f1; no_alpha_renaming_b s f2

    | PPprefix(op, f1) ->
      no_alpha_renaming_b s f1

    | PPget(f1,f2) ->
      no_alpha_renaming_b s f1; no_alpha_renaming_b s f2


    | PPset(f1, f2, f3) ->
      no_alpha_renaming_b s f1;
      no_alpha_renaming_b s f2;
      no_alpha_renaming_b s f3


    | PPextract(f1, f2, f3) ->
      no_alpha_renaming_b s f1;
      no_alpha_renaming_b s f2;
      no_alpha_renaming_b s f3

    | PPconcat(f1, f2) ->
      no_alpha_renaming_b s f1; no_alpha_renaming_b s f2

    | PPif(f1, f2, f3) ->
      no_alpha_renaming_b s f1;
      no_alpha_renaming_b s f2;
      no_alpha_renaming_b s f3

    | PPnamed(n, f1) ->
      no_alpha_renaming_b s f1

    | PPdot(f1, a) ->
      no_alpha_renaming_b s f1

    | PPrecord l ->
      List.iter (fun (_,e) -> no_alpha_renaming_b s e) l

    | PPwith(e, l) ->
      List.iter (fun (_,e) -> no_alpha_renaming_b s e) l;
      no_alpha_renaming_b s e

    | PPlet(x, f1, f2) ->
      no_alpha_renaming_b s f1;
      let s, x =
	if S.mem x up then
	  let nx = fresh_var x in
	  let m = MString.add x nx m in
	  let up = S.add nx up in
	  (up, m), nx
	else
	  (S.add x up, m), x
      in
      no_alpha_renaming_b s f2

    | PPcheck f' ->
      no_alpha_renaming_b s f'

    | PPcut f' ->
      no_alpha_renaming_b s f'

    | PPcast (f',ty) ->
      no_alpha_renaming_b s f'

    | PPforall(xs, trs, hyp, f1) ->
      let xs1, xs2 = List.partition (fun (x, _) -> S.mem x up) xs in
      let nv = List.map (fun (x, ty) -> fresh_var x, ty) xs1 in
      let m = List.fold_left2
	(fun m (x, _) (nx, _) -> MString.add x nx m) m xs1 nv in
      let xs = nv @ xs2 in
      let up = List.fold_left (fun up (x, _) -> S.add x up) up xs in
      let s = (up, m) in
      List.iter (no_alpha_renaming_b s) hyp;
      no_alpha_renaming_b s f1;
      List.iter (fun (l, _) -> List.iter (no_alpha_renaming_b s) l) trs

    | PPforall_named (xs, trs, hyp, f1) ->
      let xs1, xs2 = List.partition (fun (x, _, _) -> S.mem x up) xs in
      let nv = List.map (fun (x, lbl, ty) -> fresh_var x, lbl, ty) xs1 in
      let m = List.fold_left2
	(fun m (x, _, _) (nx, _, _) -> MString.add x nx m) m xs1 nv in
      let xs = nv @ xs2 in
      let up = List.fold_left (fun up (x, _, _) -> S.add x up) up xs in
      let s = (up, m) in
      List.iter (no_alpha_renaming_b s) hyp;
      no_alpha_renaming_b s f1;
      List.iter (fun (l, _) -> List.iter (no_alpha_renaming_b s) l) trs

    | PPexists(lx, trs, hyp, f1) ->
      let s, lx =
	List.fold_left
	  (fun (s, lx) (x, _) ->
	    if S.mem x up then
	      let nx = fresh_var x in
	      let m = MString.add x nx m in
	      let up = S.add nx up in
	      (up, m), nx :: lx
	    else
	      (S.add x up, m), x :: lx)
	  (s, []) lx
      in
      no_alpha_renaming_b s f1;
      List.iter (no_alpha_renaming_b s) hyp;
      List.iter (fun (l, _) -> List.iter (no_alpha_renaming_b s) l) trs

    | PPexists_named (lx, trs, hyp, f1) ->
      let s, lx =
	List.fold_left
	  (fun (s, lx) (x, _, _) ->
	    if S.mem x up then
	      let nx = fresh_var x in
	      let m = MString.add x nx m in
	      let up = S.add nx up in
	      (up, m), nx :: lx
	    else
	      (S.add x up, m), x :: lx)
	  (s, []) lx
      in
      no_alpha_renaming_b s f1;
      List.iter (no_alpha_renaming_b s) hyp;
      List.iter (fun (l, _) -> List.iter (no_alpha_renaming_b s) l) trs

let rec alpha_renaming_b ((up, m) as s) f =
  match f.pp_desc with
    | PPvar x ->
      (try
         let y = MString.find x m in
         assert (String.compare x y <> 0);
         {f with pp_desc = PPvar y}
       with Not_found -> f)

    | PPmapsTo (x, e) ->
      let x' =
        try
          let y = MString.find x m in
          assert (String.compare x y <> 0);
          y
        with Not_found -> x
      in
      let e' = alpha_renaming_b s e in
      if x == x' && e == e' then f
      else {f with pp_desc = PPmapsTo(x', e')}

    | PPapp(k, l) ->
      let l2 = List.rev (List.rev_map (alpha_renaming_b s) l) in
      if List.for_all2 (fun a b -> a == b) l l2 then f
      else {f with pp_desc = PPapp(k, l2)}

    | PPinInterval (e,a,b,c,d) ->
      let e' = alpha_renaming_b s e in
      if e == e' then e
      else {f with pp_desc = PPinInterval(e', a,b,c,d)}

    | PPdistinct l ->
      let l2 = List.rev (List.rev_map (alpha_renaming_b s) l) in
      if List.for_all2 (fun a b -> a == b) l l2 then f
      else {f with pp_desc = PPdistinct l2}

    | PPconst _ -> f

    | PPinfix(f1, op, f2) ->
      let ff1 = alpha_renaming_b s f1 in
      let ff2 = alpha_renaming_b s f2 in
      if f1 == ff1 && f2 == ff2 then f
      else {f with pp_desc = PPinfix(ff1, op, ff2)}

    | PPprefix(op, f1) ->
      let ff1 = alpha_renaming_b s f1 in
      if f1 == ff1 then f
      else {f with pp_desc = PPprefix(op, ff1)}

    | PPget(f1,f2) ->
      let ff1 = alpha_renaming_b s f1 in
      let ff2 = alpha_renaming_b s f2 in
      if f1 == ff1 && f2 == ff2 then f
      else {f with pp_desc = PPget(ff1, ff2)}

    | PPset(f1, f2, f3) ->
      let ff1 = alpha_renaming_b s f1 in
      let ff2 = alpha_renaming_b s f2 in
      let ff3 = alpha_renaming_b s f3 in
      if f1 == ff1 && f2 == ff2 && f3 == ff3 then f
      else {f with pp_desc = PPset(ff1, ff2, ff3)}

    | PPextract(f1, f2, f3) ->
      let ff1 = alpha_renaming_b s f1 in
      let ff2 = alpha_renaming_b s f2 in
      let ff3 = alpha_renaming_b s f3 in
      if f1 == ff1 && f2 == ff2 && f3 == ff3 then f
      else {f with pp_desc = PPextract(ff1, ff2, ff3)}

    | PPconcat(f1, f2) ->
      let ff1 = alpha_renaming_b s f1 in
      let ff2 = alpha_renaming_b s f2 in
      if ff1 == f1 && ff2 == f2 then f
      else {f with pp_desc = PPconcat(ff1, ff2)}

    | PPif(f1, f2, f3) ->
      let ff1 = alpha_renaming_b s f1 in
      let ff2 = alpha_renaming_b s f2 in
      let ff3 = alpha_renaming_b s f3 in
      if f1 == ff1 && f2 == ff2 && f3 == ff3 then f
      else {f with pp_desc = PPif(ff1, ff2, ff3)}

    | PPnamed(n, f1) ->
      let ff1 = alpha_renaming_b s f1 in
      if f1 == ff1 then f
      else {f with pp_desc = PPnamed(n, ff1)}

    | PPdot(f1, a) ->
      let ff1 = alpha_renaming_b s f1 in
      if f1 == ff1 then f
      else {f with pp_desc = PPdot(ff1, a)}

    | PPrecord l ->
      let l2 =
        List.rev (List.rev_map (fun (a,e) -> a, alpha_renaming_b s e) l) in
      if List.for_all2 (fun a b -> a == b) l l2 then f
      else {f with pp_desc = PPrecord l2}

    | PPwith(e, l) ->
      let l2 =
        List.rev (List.rev_map (fun (a,e) -> a, alpha_renaming_b s e) l) in
      let ee = alpha_renaming_b s e in
      if List.for_all2 (fun a b -> a == b) l l2 && e == ee then f
      else {f with pp_desc = PPwith(ee, l2)}

    | PPlet(x, f1, f2) ->
      let ff1 = alpha_renaming_b s f1 in
      let s, x =
	if S.mem x up then
	  let nx = fresh_var x in
	  let m = MString.add x nx m in
	  let up = S.add nx up in
	  (up, m), nx
	else
	  (S.add x up, m), x
      in
      let ff2 = alpha_renaming_b s f2 in
      if f1 == ff1 && f2 == ff2 then f
      else {f with pp_desc = PPlet(x, ff1, ff2)}

    | PPcheck f' ->
      let ff = alpha_renaming_b s f' in
      if f' == ff then f
      else {f with pp_desc = PPcheck ff}

    | PPcut f' ->
      let ff = alpha_renaming_b s f' in
      if f' == ff then f
      else {f with pp_desc = PPcut ff}

    | PPcast (f',ty) ->
      let ff = alpha_renaming_b s f' in
      if f' == ff then f
      else {f with pp_desc = PPcast (ff,ty)}

    | PPforall(xs, trs, hyp, f1) ->
      let xs1, xs2 = List.partition (fun (x, _) -> S.mem x up) xs in
      let nv = List.map (fun (x, ty) -> fresh_var x, ty) xs1 in
      let m = List.fold_left2
	(fun m (x, _) (nx, _) -> MString.add x nx m) m xs1 nv in
      let xs = nv @ xs2 in
      let up = List.fold_left (fun up (x, _) -> S.add x up) up xs in
      let s = (up, m) in
      let ff1 = alpha_renaming_b s f1 in
      let trs2 =
        List.map (fun (l, tuser) ->
          List.map (alpha_renaming_b s) l, tuser) trs
      in
      let hyp2 = List.map (alpha_renaming_b s) hyp in
      if f1==ff1 && List.for_all2 (fun a b -> a==b) trs trs2
        && List.for_all2 (fun a b -> a==b) hyp hyp2 then f
      else {f with pp_desc = PPforall(xs, trs2, hyp2, ff1)}

    | PPforall_named (xs, trs, hyp, f1) ->
      let xs1, xs2 = List.partition (fun (x, _, _) -> S.mem x up) xs in
      let nv = List.map (fun (x, lbl, ty) -> fresh_var x, lbl, ty) xs1 in
      let m = List.fold_left2
	(fun m (x, _, _) (nx, _, _) -> MString.add x nx m) m xs1 nv in
      let xs = nv @ xs2 in
      let up = List.fold_left (fun up (x, _, _) -> S.add x up) up xs in
      let s = (up, m) in
      let ff1 = alpha_renaming_b s f1 in
      let trs2 =
        List.map (fun (l, tuser) ->
          List.map (alpha_renaming_b s) l, tuser) trs
      in
      let hyp2 = List.map (alpha_renaming_b s) hyp in
      if f1==ff1 && List.for_all2 (fun a b -> a==b) trs trs2
        && List.for_all2 (fun a b -> a==b) hyp hyp2 then f
      else {f with pp_desc = PPforall_named (xs, trs2, hyp2, ff1)}

    | PPexists(lx, trs, hyp, f1) ->
      let s, lx =
	List.fold_left
	  (fun (s, lx) (x, ty) ->
	    if S.mem x up then
	      let nx = fresh_var x in
	      let m = MString.add x nx m in
	      let up = S.add nx up in
	      (up, m), (nx, ty) :: lx
	    else
	      (S.add x up, m), (x, ty) :: lx)
	  (s, []) lx
      in
      let trs2 =
        List.map
          (fun (l, tuser) -> List.map (alpha_renaming_b s) l, tuser) trs
      in
      let ff1 = alpha_renaming_b s f1 in
      let hyp2 = List.map (alpha_renaming_b s) hyp in
      if f1==ff1 && List.for_all2 (fun a b -> a==b) trs trs2
        && List.for_all2 (fun a b -> a==b) hyp hyp2 then f
      else {f with pp_desc = PPexists(lx, trs2, hyp2, ff1)}

    | PPexists_named (lx, trs, hyp, f1) ->
      let s, lx =
	List.fold_left
	  (fun (s, lx) (x, lbl, ty) ->
	    if S.mem x up then
	      let nx = fresh_var x in
	      let m = MString.add x nx m in
	      let up = S.add nx up in
	      (up, m), (nx, lbl, ty) :: lx
	    else
	      (S.add x up, m), (x, lbl, ty) :: lx)
	  (s, []) lx
      in
      let ff1 = alpha_renaming_b s f1 in
      let trs2 =
        List.map
          (fun (l, tuser) -> List.map (alpha_renaming_b s) l, tuser) trs
      in
      let hyp2 = List.map (alpha_renaming_b s) hyp in
      if f1==ff1 && List.for_all2 (fun a b -> a==b) trs trs2
        && List.for_all2 (fun a b -> a==b) hyp hyp2 then f
      else {f with pp_desc = PPexists_named (lx, trs2, hyp2, ff1)}


let alpha_renaming_b s f =
  try no_alpha_renaming_b s f; f
  with Exit -> alpha_renaming_b s f

let alpha_renaming = alpha_renaming_b (S.empty, MString.empty)

let alpha_renaming_env env =
  let up = MString.fold (fun s _ up -> S.add s up)
    env.Env.logics S.empty in
  let up = MString.fold (fun s _ up -> S.add s up) env.Env.var_map up in
  alpha_renaming_b (up, MString.empty)


let inv_infix = function
  | PPand -> PPor | PPor -> PPand | _ -> assert false

let rec elim_toplevel_forall env bnot f =
  (* bnot = true : nombre impaire de not *)
  match f.pp_desc with
    | PPforall (lv, _, _, f) when bnot ->
      let env = List.fold_left (fun env (v, ty) ->
          Env.add_names env [v] ty f.pp_loc
        ) env lv in
      elim_toplevel_forall env bnot f

    | PPforall_named (lvb, _, _, f) when bnot->
      let env = List.fold_left (fun env (v, lbl, ty) ->
          Env.add_names_lbl env [v, lbl] ty f.pp_loc
        ) env lvb in
      elim_toplevel_forall env bnot f

    | PPinfix (f1, PPand, f2) when not bnot ->
      let f1 , env = elim_toplevel_forall env false f1 in
      let f2 , env = elim_toplevel_forall env false
	(alpha_renaming_env env f2) in
      { f with pp_desc = PPinfix(f1, PPand , f2)}, env

    | PPinfix (f1, PPor, f2) when bnot ->
      let f1 , env = elim_toplevel_forall env true f1 in
      let f2 , env = elim_toplevel_forall env true
	(alpha_renaming_env env f2) in
      { f with pp_desc = PPinfix(f1, PPand , f2)}, env

    | PPinfix (f1, PPimplies, f2) when bnot ->
      let f1 , env = elim_toplevel_forall env false f1 in
      let f2 , env = elim_toplevel_forall env true
	(alpha_renaming_env env f2) in
      { f with pp_desc = PPinfix(f1,PPand,f2)}, env

    | PPprefix (PPnot, f) -> elim_toplevel_forall env (not bnot) f


    | _ when bnot ->
      { f with pp_desc = PPprefix (PPnot, f) }, env

    | _  -> f , env


let rec intro_hypothesis env valid_mode f =
  match f.pp_desc with
    | PPinfix(f1,PPimplies,f2) when valid_mode ->
      let ((f1, env) as f1_env) =
	elim_toplevel_forall env (not valid_mode) f1 in
      let axioms, goal = intro_hypothesis env valid_mode
	(alpha_renaming_env env f2) in
      f1_env::axioms, goal
    | PPlet(var,{pp_desc=PPcast(t1,ty); pp_loc = ty_loc},f2) ->
      let env = Env.add_names env [var] ty ty_loc in
      let var = {pp_desc = PPvar var; pp_loc = f.pp_loc} in
      let feq = {pp_desc = PPinfix(var,PPeq,t1); pp_loc = f.pp_loc} in
      let axioms, goal = intro_hypothesis env valid_mode
	(alpha_renaming_env env f2) in
      (feq,env)::axioms, goal
    | PPforall (lv, _, _, f) when valid_mode ->
      let env = List.fold_left (fun env (v, ty) ->
          Env.add_names env [v] ty f.pp_loc
        ) env lv in
      intro_hypothesis env valid_mode f
    | PPexists (lv, _, _, f) when not valid_mode->
      let env = List.fold_left (fun env (v, ty) ->
          Env.add_names env [v] ty f.pp_loc
        ) env lv in
      intro_hypothesis env valid_mode f
    | PPforall_named (lvb, _, _, f) when valid_mode ->
      let env = List.fold_left (fun env (v, lbl, ty) ->
          Env.add_names_lbl env [v, lbl] ty f.pp_loc
        ) env lvb in
      intro_hypothesis env valid_mode f
    | PPexists_named (lvb, _, _, f) when not valid_mode->
      let env = List.fold_left (fun env (v, lbl, ty) ->
          Env.add_names_lbl env [v, lbl] ty f.pp_loc
        ) env lvb in
      intro_hypothesis env valid_mode f
    | _ ->
      let f_env = elim_toplevel_forall env valid_mode f in
      [] , f_env

let fresh_hypothesis_name =
  let cpt = ref 0 in
  fun sort ->
    incr cpt;
    match sort with
      | Thm -> "@H"^(string_of_int !cpt)
      | _ -> "@L"^(string_of_int !cpt)

let fresh_check_name =
  let cpt = ref 0 in fun () -> incr cpt; "check_"^(string_of_int !cpt)

let fresh_cut_name =
  let cpt = ref 0 in fun () -> incr cpt; "cut_"^(string_of_int !cpt)

let check_duplicate_params l =
  let rec loop l acc =
    match l with
      | [] -> ()
      | (loc,x,_)::rem ->
	if List.mem x acc then
	  error (ClashParam x) loc
	else loop rem (x::acc)
  in
  loop l []

let rec make_pred loc trs f = function
[] ->  f
  | [x,t] ->
    { pp_desc = PPforall([x,t],trs,[],f) ; pp_loc = loc }
  | (x,t)::l ->
    { pp_desc = PPforall([x,t],[],[],(make_pred loc trs f l)) ;
      pp_loc = loc }

let rec max_terms acc f =
  match f.pp_desc with
    | PPinfix(f1, ( PPand | PPor | PPimplies | PPiff ), f2)
    | PPconcat(f1, f2) ->
      let acc = max_terms acc f1 in
      max_terms acc f2

    | PPforall(_, _, _, _)
    | PPexists(_, _, _, _)
    | PPforall_named(_, _, _, _)
    | PPexists_named(_, _, _, _)
    | PPvar _
    | PPlet(_, _, _)
    | PPinfix(_, _, _) -> raise Exit

    | PPif(f1, f2, f3) ->
      let acc = max_terms acc f1 in
      let acc = max_terms acc f2 in
      max_terms acc f3
    | PPextract(f1, _, _) | PPprefix(_, f1)
    | PPnamed(_, f1) ->
      max_terms acc f1
    | _ -> f::acc

let max_terms f = try max_terms [] f with Exit -> []

let rec mono_term {c = {tt_ty=tt_ty; tt_desc=tt_desc}; annot = id} =
  let tt_desc = match tt_desc with
    | TTconst _ | TTvar _ ->
      tt_desc
    | TTinfix (t1, sy, t2) ->
      TTinfix(mono_term t1, sy, mono_term t2)
    | TTprefix (sy,t) ->
      TTprefix(sy, mono_term t)
    | TTapp (sy,tl) ->
      TTapp (sy, List.map mono_term tl)
    | TTinInterval (e, a,b,c,d) ->
      TTinInterval(mono_term e, a,b,c,d)
    | TTmapsTo (x, e) ->
      TTmapsTo(x, mono_term e)
    | TTget (t1,t2) ->
      TTget (mono_term t1, mono_term t2)
    | TTset (t1,t2,t3) ->
      TTset(mono_term t1, mono_term t2, mono_term t3)
    | TTextract (t1,t2,t3) ->
      TTextract(mono_term t1, mono_term t2, mono_term t3)
    | TTconcat (t1,t2)->
      TTconcat (mono_term t1, mono_term t2)
    | TTdot (t1, a) ->
      TTdot (mono_term t1, a)
    | TTrecord lbs ->
      TTrecord (List.map (fun (x, t) -> x, mono_term t) lbs)
    | TTlet (sy,t1,t2)->
      TTlet (sy, mono_term t1, mono_term t2)
    | TTnamed (lbl, t)->
      TTnamed (lbl, mono_term t)
  in
  { c = {tt_ty = Ty.monomorphize tt_ty; tt_desc=tt_desc}; annot = id}


let monomorphize_atom tat =
  let c = match tat.c with
    | TAtrue | TAfalse -> tat.c
    | TAeq tl -> TAeq (List.map mono_term tl)
    | TAneq tl -> TAneq (List.map mono_term tl)
    | TAle tl -> TAle (List.map mono_term tl)
    | TAlt tl -> TAlt (List.map mono_term tl)
    | TAdistinct tl -> TAdistinct (List.map mono_term tl)
    | TApred t -> TApred (mono_term t)
    | TAbuilt (hs, tl) -> TAbuilt(hs, List.map mono_term tl)
  in
  { tat with c = c }

let monomorphize_var (s,ty) = s, Ty.monomorphize ty

let rec monomorphize_form tf =
  let c = match tf.c with
    | TFatom tat -> TFatom (monomorphize_atom tat)
    | TFop (oplogic , tfl) ->
      TFop(oplogic, List.map monomorphize_form tfl)
    | TFforall qf ->
      TFforall
        {  qf_bvars = List.map monomorphize_var qf.qf_bvars;
           qf_upvars = List.map monomorphize_var qf.qf_upvars;
           qf_hyp = List.map monomorphize_form qf.qf_hyp;
           qf_form = monomorphize_form qf.qf_form;
           qf_triggers =
            List.map (fun (l, b) -> List.map mono_term l, b) qf.qf_triggers}
    | TFexists qf ->
      TFexists
        {  qf_bvars = List.map monomorphize_var qf.qf_bvars;
           qf_upvars = List.map monomorphize_var qf.qf_upvars;
           qf_hyp = List.map monomorphize_form qf.qf_hyp;
           qf_form = monomorphize_form qf.qf_form;
           qf_triggers =
            List.map (fun (l, b) -> List.map mono_term l, b) qf.qf_triggers}
    | TFlet (l, sy, tt, tf) ->
      let l = List.map monomorphize_var l in
      TFlet(l,sy, mono_term tt, monomorphize_form tf)
    | TFnamed (hs,tf) ->
      TFnamed(hs, monomorphize_form tf)
  in
  { tf with c = c }

let axioms_of_rules keep_triggers loc name lf acc env =
  let acc =
    List.fold_left
      (fun acc (f, _) ->
        let f = Triggers.make keep_triggers false f in
        let name = (Hstring.fresh_string ()) ^ "_" ^ name in
        let td = {c = TAxiom(loc,name,Default, f); annot = new_id () } in
	(td, env)::acc
      ) acc lf
  in
  acc, env



let type_hypothesis keep_triggers acc env_f loc sort f =
  let f,_ = type_form env_f f in
  let f = monomorphize_form f in
  let f = Triggers.make keep_triggers false f in
  let td =
    {c = TAxiom(loc, fresh_hypothesis_name sort,Default, f);
     annot = new_id () } in
  (td, env_f)::acc


let type_goal keep_triggers acc env_g loc sort n goal =
  let goal, _ = type_form env_g goal in
  let goal = monomorphize_form goal in
  let goal = Triggers.make keep_triggers true goal in
  let td = {c = TGoal(loc, sort, n, goal); annot = new_id () } in
  (td, env_g)::acc


let rec type_and_intro_goal keep_triggers acc env loc sort n f =
  let b = (* smtfile() || smt2file() || satmode()*) false in
  let axioms, (goal, env_g) =
    intro_hypothesis env (not b) f in
  let loc = f.pp_loc in
  let acc =
    List.fold_left
      (fun acc (f, env_f) -> match f.pp_desc with
	| PPcut f ->
	  let acc = type_and_intro_goal keep_triggers acc env_f
	    loc Cut (fresh_cut_name ()) f in
	  type_hypothesis keep_triggers acc env_f loc sort f

	| PPcheck f ->
	  type_and_intro_goal keep_triggers acc env_f
	    loc Check (fresh_check_name ()) f

	| _ ->
	  type_hypothesis keep_triggers acc env_f loc sort f
      ) acc axioms
  in
  type_goal keep_triggers acc env_g loc sort n goal



let type_one_th_decl keep_triggers env e =
  (* NB: we always keep triggers for axioms of theories *)
  match e with
  | Axiom(loc,name,ax_kd,f)  ->
     let f,_ = type_form ~in_theory:true env f in
     let f = Triggers.make (*keep_triggers=*) true false f in
     {c = TAxiom (loc,name,ax_kd,f); annot = new_id ()}

  | Theory (loc, _, _, _)
  | Logic (loc, _, _, _)
  | Rewriting(loc, _, _)
  | Goal(loc, _, _)
  | Predicate_def(loc,_,_,_)
  | Function_def(loc,_,_,_,_)
  | TypeDecl(loc, _, _, _) ->
    error WrongDeclInTheory loc


let type_decl keep_triggers (acc, env) d =
  Types.to_tyvars := MString.empty;
  try
    match d with
      | Theory (loc, name, ext, l) ->
	 Options.tool_req 1 "TR-Typing-TheoryDecl$_F$";
	let tl = List.map (type_one_th_decl keep_triggers env) l in
        let ext = Typed.th_ext_of_string ext loc in
	let td = {c = TTheory(loc, name, ext, tl); annot = new_id () } in
	(td, env)::acc, env

      | Logic (loc, ac, lp, pp_ty) ->
	Options.tool_req 1 "TR-Typing-LogicFun$_F$";
	let env' = Env.add_logics env ac lp pp_ty loc in
	let lp = List.map fst lp in
	let td = {c = TLogic(loc,lp,pp_ty); annot = new_id () } in
	(td, env)::acc, env'

      | Axiom(loc,name,ax_kd,f) ->
	Options.tool_req 1 "TR-Typing-AxiomDecl$_F$";
	let f, _ = type_form env f in
	let f = Triggers.make keep_triggers false f in
	let td = {c = TAxiom(loc,name,ax_kd,f); annot = new_id () } in
	(td, env)::acc, env

      | Rewriting(loc, name, lr) ->
	let lf = List.map (type_form env) lr in
        if Options.rewriting () then
          let rules = List.map (fun (f,_) -> make_rules loc f) lf in
	  let td = {c = TRewriting(loc, name, rules); annot = new_id () } in
	  (td, env)::acc, env
        else
          axioms_of_rules keep_triggers loc name lf acc env


      | Goal(loc, n, f) ->
        Options.tool_req 1 "TR-Typing-GoalDecl$_F$";
	(*let f = move_up f in*)
	let f = alpha_renaming_env env f in
 	type_and_intro_goal keep_triggers acc env loc Thm n f, env

      | Predicate_def(loc,n,l,e)
      | Function_def(loc,n,l,_,e) ->
	check_duplicate_params l;
	let ty =
	  let l = List.map (fun (_,_,x) -> x) l in
	  match d with
	      Function_def(_,_,_,t,_) -> PFunction(l,t)
	    | _ -> PPredicate l
	in
	let l = List.map (fun (_,x,t) -> (x,t)) l in

	let env = Env.add_logics env Symbols.Other [n] ty loc in (* TODO *)

	let n = fst n in

	let lvar = List.map (fun (x,_) -> {pp_desc=PPvar x;pp_loc=loc}) l in
	let p = {pp_desc=PPapp(n,lvar) ; pp_loc=loc } in
	let infix = match d with Function_def _ -> PPeq | _ -> PPiff in
	let f = { pp_desc = PPinfix(p,infix,e) ; pp_loc = loc } in
	(* le trigger [[p]] ne permet pas de replier la definition,
	   donc on calcule les termes maximaux de la definition pour
	   laisser une possibilite de replier *)
	let trs = max_terms e in
	let f = make_pred loc [[p], false ; trs, false] f l in
	let f,_ = type_form env f in
	let f = Triggers.make keep_triggers false f in
	let td =
	  match d with
	    | Function_def(_,_,_,t,_) ->
	      Options.tool_req 1 "TR-Typing-LogicFun$_F$";
	      TFunction_def(loc,n,l,t,f)
	    | _ ->
	      Options.tool_req 1 "TR-Typing-LogicPred$_F$";
	      TPredicate_def(loc,n,l,f)
	in
	let td_a = { c = td; annot=new_id () } in
	(td_a, env)::acc, env

      | TypeDecl(loc, ls, s, body) ->
	Options.tool_req 1 "TR-Typing-TypeDecl$_F$";
	let env1 = Env.add_type_decl env ls s body loc in
	let td1 =  TTypeDecl(loc, ls, s, body) in
	let td1_a = { c = td1; annot=new_id () } in
        let tls = List.map (fun s -> PPTvarid (s,loc)) ls in
	let ty = PFunction([], PPTexternal(tls, s, loc)) in
	match body with
	  | Enum lc ->
	    let lcl = List.map (fun c -> c, "") lc in (* TODO change this *)
	    let env2 = Env.add_logics env1 Symbols.Constructor lcl ty loc in
	    let td2 = TLogic(loc, lc, ty) in
	    let td2_a = { c = td2; annot=new_id () } in
	    (td1_a, env1)::(td2_a,env2)::acc, env2
	  | _ -> (td1_a, env1)::acc, env1

  with Warning(e,loc) ->
    Loc.report std_formatter loc;
    acc, env

let file keep_triggers env ld =
  let ltd, env =
    List.fold_left
      (fun acc d -> type_decl keep_triggers acc d)
      ([], env) ld
  in
  List.rev ltd, env

let is_local_hyp s =
  try Pervasives.(=) (String.sub s 0 2) "@L" with Invalid_argument _ -> false

let is_global_hyp s =
  try Pervasives.(=) (String.sub s 0 2) "@H" with Invalid_argument _ -> false

let split_goals l =
  let _, _, _, ret =
    List.fold_left
      (fun (ctx, global_hyp, local_hyp, ret) ( (td, env) as x) ->
	match td.c with
	  | TGoal (_, (Check | Cut), _, _) ->
	    ctx, global_hyp, [], (x::(local_hyp@global_hyp@ctx))::ret

	  | TGoal (_, _, _, _) ->
	    ctx, [], [], (x::(local_hyp@global_hyp@ctx))::ret

	  | TAxiom (_, s, _, _) when is_global_hyp s ->
	    ctx, x::global_hyp, local_hyp, ret

	  | TAxiom (_, s, _, _) when is_local_hyp s ->
	    ctx, global_hyp, x::local_hyp, ret

	  | _ -> x::ctx, global_hyp, local_hyp, ret
      ) ([],[],[],[]) l
  in
  List.rev_map List.rev ret

let term env vars t =
  let vmap =
    List.fold_left
      (fun m (s,ty)->
	let str = Symbols.to_string_clean s in
	MString.add str (s,ty) m
      ) env.Env.var_map vars in
  let env = { env with Env.var_map = vmap } in
  type_term env t

type env = Env.t

let empty_env = Env.empty
