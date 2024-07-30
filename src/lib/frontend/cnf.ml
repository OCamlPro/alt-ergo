(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module E = Expr
module Sy = Symbols
module SE = E.Set

let varset_of_list =
  List.fold_left
    (fun acc (s,ty) ->
       let v =
         match s with
         | Sy.Var v -> v
         | _ -> assert false
       in
       Var.Map.add v (Ty.shorten ty) acc
    ) Var.Map.empty

module ME =
  Map.Make
    (struct
      type t = E.t
      let compare a b =
        let c = E.depth a - E.depth b in
        if c <> 0 then c
        else E.compare a b
    end)

let rec make_term quant_basename t =
  let rec mk_term ({ c = { tt_ty = ty; tt_desc = tt; _ }; _ }
                   : (_ Typed.tterm, _) Typed.annoted) =
    let ty = Ty.shorten ty in
    match tt with
    | TTconst Ttrue ->
      E.vrai
    | TTconst Tfalse ->
      E.faux
    | TTconst Tvoid ->
      E.void
    | TTconst (Tint i) ->
      E.int i
    | TTconst (Treal n) ->
      E.real (Numbers.Q.to_string n)
    | TTconst (Tbitv bt) ->
      E.bitv bt ty
    | TTvar s -> E.mk_term s [] ty
    | TTapp (s, l) ->
      E.mk_term s (List.map mk_term l) ty

    | TTinInterval (e, lb, ub) ->
      assert (ty == Ty.Tbool);
      E.mk_term (Sy.mk_in lb ub) [mk_term e] ty

    | TTmapsTo (x, e) ->
      assert (ty == Ty.Tbool);
      E.mk_term (Sy.mk_maps_to x) [mk_term e] ty

    | TTinfix (t1, s, t2) ->
      begin
        let t2 = mk_term t2 in (*keep old mk_term order -> avoid regression*)
        let t1 = mk_term t1 in
        E.mk_term s [t1; t2] ty
      end

    | TTprefix ((Sy.Op Sy.Minus) as s, n) ->
      let t1 = if ty == Ty.Tint then E.int "0" else E.real "0"  in
      E.mk_term s [t1; mk_term n] ty
    | TTprefix _ ->
      assert false

    | TTget (t1, t2) ->
      E.mk_term (Sy.Op Sy.Get)
        [mk_term t1; mk_term t2] ty

    | TTset (t1, t2, t3) ->
      let t1 = mk_term t1 in
      let t2 = mk_term t2 in
      let t3 = mk_term t3 in
      E.mk_term (Sy.Op Sy.Set) [t1; t2; t3] ty

    | TTextract (t1, i, j) ->
      let t1 = mk_term t1 in
      E.mk_term (Sy.Op (Sy.Extract (i, j))) [t1] ty

    | TTconcat (t1, t2) ->
      E.mk_term (Sy.Op Sy.Concat)
        [mk_term t1; mk_term t2] ty

    | TTdot (t, s) ->
      E.mk_term (Sy.Op (Sy.Access (Uid.of_hstring s))) [mk_term t] ty

    | TTrecord lbs ->
      let lbs = List.map (fun (_, t) -> mk_term t) lbs in
      E.mk_record lbs ty

    | TTlet (binders, t2) ->
      let binders =
        List.rev_map (fun (s, t1) ->
            (* Remark: the parser ensures that binders' symbol are always
               variables. We could modify the typechecker module to
               produce the appropriate type for binders, that is `Var.t list`,
               but this requires a large amount of modifications in the
               typechecker, which is a legacy part of our codebase.

               See PR: https://github.com/OCamlPro/alt-ergo/pull/976. *)
            match s with Sy.Var v -> v, mk_term t1 | _ -> assert false)
          (List.rev binders)
      in
      List.fold_left
        (fun acc (v, e) ->
           E.mk_let v e acc
           [@ocaml.ppwarning "TODO: should introduce fresh vars"]
        )(mk_term t2) binders

    | TTnamed(lbl, t) ->
      let t = mk_term t in
      E.add_label lbl t;
      t

    | TTite(cond, t1, t2) ->
      let cond =
        make_form
          quant_basename cond Loc.dummy
          ~decl_kind:E.Daxiom (* not correct, but not a problem *)
          ~toplevel:false
      in
      let t1 = mk_term t1 in
      let t2 = mk_term t2 in
      E.mk_ite cond t1 t2

    | TTproject (t, s) ->
      E.mk_term (Sy.destruct (Uid.of_hstring s)) [mk_term t] ty

    | TTmatch (e, pats) ->
      let e = make_term quant_basename e in
      let pats =
        List.rev_map (fun (p, t) ->
            p, make_term quant_basename t) (List.rev pats)
      in
      E.mk_match e pats

    | TTform e ->
      make_form
        quant_basename e Loc.dummy
        ~decl_kind:E.Daxiom (* not correct, but not a problem *)
        ~toplevel:false
  in
  mk_term t


and make_trigger ~in_theory name quant_basename hyp (e, from_user) =
  let content = List.map (make_term quant_basename) e in
  (* clean trigger:
     remove useless terms in multi-triggers after inlining of lets*)
  let trigger = E.mk_trigger ~user:from_user ~hyp content in
  E.clean_trigger ~in_theory name trigger

and make_form name_base ~toplevel f loc ~decl_kind : E.t =
  let name_tag = ref 0 in
  let rec mk_form ~toplevel (c : _ Typed.tform) =
    match c with
    | TFatom a ->
      begin match a.c with
        | TAtrue ->
          E.vrai
        | TAfalse ->
          E.faux
        | TAeq [t1;t2] ->
          E.mk_eq ~iff:true
            (make_term name_base t1)
            (make_term name_base t2)
        | TApred (t, negated) ->
          let res = make_term name_base t in
          if negated then E.neg res else res

        | TAneq lt | TAdistinct lt ->
          let lt = List.map (make_term name_base) lt in
          E.mk_distinct ~iff:true lt
        | TAle [t1;t2] ->
          E.mk_builtin ~is_pos:true Sy.LE
            [make_term name_base t1;
             make_term name_base t2]
        | TAlt [t1;t2] ->
          begin match t1.c.tt_ty with
            | Ty.Tint ->
              let one : (_ Typed.tterm, _) Typed.annoted =
                {c = {tt_ty = Ty.Tint;
                      tt_desc = TTconst(Tint "1")}; annot = t1.annot} in
              let tt2 =
                E.mk_term (Sy.Op Sy.Minus)
                  [make_term name_base t2;
                   make_term name_base one]
                  Ty.Tint
              in
              E.mk_builtin ~is_pos:true Sy.LE
                [make_term name_base t1; tt2]
            | _ ->
              E.mk_builtin ~is_pos:true Sy.LT
                [make_term name_base t1;
                 make_term name_base t2]
          end
        | TTisConstr (t, lbl) ->
          E.mk_builtin ~is_pos:true (Sy.IsConstr (Uid.of_hstring lbl))
            [make_term name_base t]

        | _ -> assert false
      end

    | TFop(((OPand | OPor | OPxor) as op),[f1;f2]) ->
      let ff1 = mk_form ~toplevel:false f1.c in
      let ff2 = mk_form ~toplevel:false f2.c in
      begin match op with
        | OPand -> E.mk_and ff1 ff2 false
        | OPor -> E.mk_or ff1 ff2 false
        | OPxor -> E.mk_xor ff1 ff2
        | _ -> assert false
      end
    | TFop(OPimp,[f1;f2]) ->
      let ff1 = mk_form ~toplevel:false f1.c in
      let ff2 = mk_form ~toplevel:false f2.c in
      E.mk_imp ff1 ff2
    | TFop(OPnot,[f]) ->
      E.neg @@ mk_form ~toplevel:false f.c
    | TFop(OPif, [cond; f2;f3]) ->
      let cond = mk_form ~toplevel:false cond.c in
      let ff2  = mk_form ~toplevel:false f2.c in
      let ff3  = mk_form ~toplevel:false f3.c in
      E.mk_if cond ff2 ff3
    | TFop(OPiff,[f1;f2]) ->
      let ff1 = mk_form ~toplevel:false f1.c in
      let ff2 = mk_form ~toplevel:false f2.c in
      E.mk_iff ff1 ff2
    | (TFforall qf | TFexists qf) as f ->
      let name =
        if !name_tag = 0 then name_base
        else Format.sprintf "#%s#sub-%d" name_base !name_tag
      in
      incr name_tag;
      let binders = varset_of_list qf.qf_bvars in
      let ff = mk_form ~toplevel:false qf.qf_form.c in

      (* S : Formulas are purified afterwards.
         Purification binds literals & formulas inside terms by
         to fresh variables.
         This purification may omit some expressions in quantified
         formulas, hence a purification step is made here, just before
         creating the said quantification.

         TODO : on-the-fly purification
      *)
      let ff = E.purify_form ff in

      let hyp =
        List.map (fun (f : _ Typed.annoted) ->
            mk_form ~toplevel:false f.c) qf.qf_hyp
      in
      let in_theory = decl_kind == E.Dtheory in
      let trs =
        List.map
          (make_trigger ~in_theory name name_base hyp) qf.qf_triggers in
      let func = match f with
        | TFforall _ -> E.mk_forall
        | TFexists _ -> E.mk_exists
        | _ -> assert false
      in
      func name loc binders trs ff ~toplevel ~decl_kind

    | TFlet(binders,lf) ->
      let binders =
        List.rev_map
          (fun (v, (e : _ Typed.tlet_kind))  ->
             v,
             match e with
             | TletTerm t -> make_term name_base t
             | TletForm g -> mk_form ~toplevel:false g.c
          )(List.rev binders)
      in
      let res = mk_form ~toplevel:false lf.c in
      List.fold_left
        (fun acc (v, e) ->
           E.mk_let v e acc
           [@ocaml.ppwarning "TODO: should introduce fresh vars"]
        )res binders

    | TFnamed(lbl, f) ->
      let ff = mk_form ~toplevel:false f.c in
      E.add_label lbl ff;
      ff

    | TFmatch (e, pats) ->
      let e = make_term name_base e in
      let pats =
        List.rev_map (fun (p, (f : _ Typed.annoted)) ->
            p, mk_form ~toplevel:false f.c)
          (List.rev pats)
      in
      E.mk_match e pats

    | _ -> assert false
  in
  mk_form ~toplevel f.c

(* wrapper of function make_form *)
let make_form name f loc ~decl_kind =
  let ff =
    make_form name f loc ~decl_kind ~toplevel:true
  in
  assert (Var.Map.is_empty (E.free_vars ff Var.Map.empty));
  let ff = E.purify_form ff in
  if Ty.Svty.is_empty (E.free_type_vars ff) then ff
  else
    E.mk_forall name loc Var.Map.empty [] ff ~toplevel:true ~decl_kind

let mk_assume acc f name loc =
  let ff = make_form name f loc ~decl_kind:E.Daxiom in
  Commands.{st_decl=Assume(name, ff, true) ; st_loc=loc} :: acc

let mk_optimize acc obj is_max loc =
  let e = make_term "" obj in
  let fn = Objective.Function.mk ~is_max e in
  Commands.{st_decl=Optimize fn; st_loc=loc } :: acc

(* extract defining term of the function or predicate. From the
   transformation of the parsed AST above, the typed AST is either of the
   form:
   - "forall x. defn <-> typed_e", if defn is a pred defn or returns a
     result of type bool
   - "forall x. defn = typed_e", if defn is a function defn whose
     return type is not bool

   where forall x. is optional (like in 'predicate p = q or r')
*)
let defining_term f =
  if Options.get_verbose () then
    Format.eprintf "defining term of %a@." Typed.print_formula f;
  match f.c with
  | TFforall {qf_form={c=TFop(OPiff,[{c=TFatom {c=TApred(d,_);_};_};_]); _}; _}
  | TFforall {qf_form={c=TFatom {c=TAeq[d;_];_}; _}; _}
  | TFop(OPiff,[{c=TFatom {c=TApred(d,_);_};_};_])
  | TFatom {c=TAeq[d;_];_} ->
    d
  | _ -> assert false

let mk_function acc f name loc =
  let defn = defining_term f in
  let defn = make_term "" defn in
  let ff = make_form name f loc ~decl_kind:(E.Dfunction defn) in
  Commands.{st_decl=Assume(name, ff, true) ; st_loc=loc} :: acc

let mk_preddef acc f name loc =
  let defn = defining_term f in
  let defn = make_term "" defn in
  let ff = make_form name f loc ~decl_kind: (E.Dpredicate defn) in
  Commands.{st_decl=PredDef (ff, name) ; st_loc=loc} :: acc

let mk_query acc n f loc sort =
  let ff = make_form "" f loc ~decl_kind:E.Dgoal in
  Commands.{st_decl=Query(n, ff, sort) ; st_loc=loc} :: acc

let make_rule (({rwt_left = t1; rwt_right = t2; rwt_vars = _} as r)
               : _ Typed.rwt_rule) =
  let s1 = make_term "" t1 in
  let s2 = make_term "" t2 in
  assert (E.is_pure s1);
  assert (E.is_pure s2);
  { r with rwt_left = s1; rwt_right = s2 }

let mk_theory acc l th_name extends _loc =
  List.fold_left
    (fun acc (e : (_ Typed.tdecl ,_) Typed.annoted) ->
       let loc, ax_name, f, axiom_kind =
         match e.c with
         | TAxiom (loc, name, ax_kd, f) -> loc, name, f, ax_kd
         | _ -> assert false
       in
       let ax_form = make_form ax_name f loc ~decl_kind:E.Dtheory in
       let th_elt = {Expr.th_name; axiom_kind; extends; ax_form; ax_name} in
       Commands.{st_decl=ThAssume th_elt ; st_loc=loc} :: acc
    )acc l

let make acc (d : (_ Typed.tdecl, _) Typed.annoted) =
  match d.c with
  | TPush (loc,n) -> Commands.{st_decl=Push n; st_loc=loc} :: acc
  | TPop (loc,n) -> Commands.{st_decl=Pop n; st_loc=loc} :: acc
  | TTheory(loc, name, ext, l) -> mk_theory acc l name ext loc
  | TAxiom(loc, name, Util.Default, f) -> mk_assume acc f name loc
  | TAxiom(_, _, Util.Propagator, _) -> assert false
  | TRewriting(loc, _, lr) ->
    {st_decl=RwtDef(List.map make_rule lr); st_loc=loc} :: acc
  | TGoal(loc, sort, n, f) -> mk_query acc n f loc sort
  | TPredicate_def(loc, n, _args, f) -> mk_preddef acc f n loc
  | TFunction_def(loc, n, _args, _rety, f) -> mk_function acc f n loc
  | TTypeDecl _ | TLogic _  -> acc
  | TReset _
  | TExit _ ->
    (* These cases only appear on smt2 files, which are handled by
       Solving_loop. *)
    Printer.print_wrn "Ignoring instruction %a" Typed.print_atdecl d;
    acc
  | TOptimize (loc, obj, is_max) -> mk_optimize acc obj is_max loc

let make_list l = List.fold_left make [] (List.rev l)
