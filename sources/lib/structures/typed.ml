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
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Format

[@@@ocaml.warning "-33"]
open Options


(** Anotations (used by the GUI). *)

type ('a, 'b) annoted =
  { c : 'a;
    annot : 'b }

let new_id = let r = ref 0 in fun () -> r := !r+1; !r

let mk ?(annot=new_id ()) c = { c; annot; }


(** Terms and Formulas *)

type tconstant =
  | Tint of string
  | Treal of Num.num
  | Tbitv of string
  | Ttrue
  | Tfalse
  | Tvoid

type oplogic =
    OPand | OPor | OPxor | OPimp | OPnot | OPiff
  | OPif

(** type of pattern in match construct of ADTs *)
type pattern =
  | Constr of { name : Hstring.t ; args : (Var.t * Hstring.t * Ty.t) list}
  (** A pattern case which is a constructor. [name] is the name of
      constructor. [args] contains the variables bound by this pattern
      with their correponsing destructors and types *)

  | Var of Var.t
  (** a pattern that is a variable (or underscore) *)

type 'a tterm =
  { tt_ty : Ty.t; tt_desc : 'a tt_desc }

and 'a atterm = ('a tterm, 'a) annoted

and 'a tt_desc =
  | TTconst of tconstant
  | TTvar of Symbols.t
  | TTinfix of ('a tterm, 'a) annoted * Symbols.t * ('a tterm, 'a) annoted
  | TTprefix of Symbols.t * ('a tterm, 'a) annoted
  | TTapp of Symbols.t * ('a tterm, 'a) annoted list
  | TTmapsTo of Var.t * ('a tterm, 'a) annoted
  | TTinInterval of 'a atterm * Symbols.bound * Symbols.bound

  | TTget of ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTset of
      ('a tterm, 'a) annoted * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTextract of
      ('a tterm, 'a) annoted * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTconcat of ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTdot of ('a tterm, 'a) annoted * Hstring.t
  | TTrecord of (Hstring.t * ('a tterm, 'a) annoted) list
  | TTlet of (Symbols.t * ('a tterm, 'a) annoted) list * ('a tterm, 'a) annoted
  | TTnamed of Hstring.t * ('a tterm, 'a) annoted
  | TTite of ('a tform, 'a) annoted *
             ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTproject of bool * ('a tterm, 'a) annoted  * Hstring.t
  | TTmatch of 'a atterm * (pattern * 'a atterm) list
  | TTform of 'a atform

and 'a atatom = ('a tatom, 'a) annoted

and 'a tatom =
  | TAtrue
  | TAfalse
  | TAeq of ('a tterm, 'a) annoted list
  | TAdistinct of ('a tterm, 'a) annoted list
  | TAneq of ('a tterm, 'a) annoted list
  | TAle of ('a tterm, 'a) annoted list
  | TAlt of ('a tterm, 'a) annoted list
  | TApred of ('a tterm, 'a) annoted * bool (* true <-> negated *)
  | TTisConstr of ('a tterm, 'a) annoted  * Hstring.t

and 'a quant_form = {
  (* quantified variables that appear in the formula *)
  qf_bvars : (Symbols.t * Ty.t) list ;
  qf_upvars : (Symbols.t * Ty.t) list ;
  qf_triggers : (('a tterm, 'a) annoted list * bool) list ;
  qf_hyp : ('a tform, 'a) annoted list;
  qf_form : ('a tform, 'a) annoted
}

and 'a atform = ('a tform, 'a) annoted

and 'a tform =
  | TFatom of ('a tatom, 'a) annoted
  | TFop of oplogic * (('a tform, 'a) annoted) list
  | TFforall of 'a quant_form
  | TFexists of 'a quant_form
  | TFlet of (Symbols.t * Ty.t) list *
             (Symbols.t * 'a tlet_kind) list * ('a tform, 'a) annoted
  | TFnamed of Hstring.t * ('a tform, 'a) annoted
  | TFmatch of 'a atterm * (pattern * 'a atform) list

and 'a tlet_kind =
  | TletTerm of ('a tterm, 'a) annoted
  | TletForm of ('a tform, 'a) annoted


(** Rewrite rules *)

type 'a rwt_rule = {
  rwt_vars : (Symbols.t * Ty.t) list;
  rwt_left : 'a;
  rwt_right : 'a
}

let print_rwt pp fmt r =
  Format.fprintf fmt "@<hv>%a@ --> %a@]" pp r.rwt_left pp r.rwt_right


(** Goal sort *)

type goal_sort = Cut | Check | Thm

let print_goal_sort fmt = function
  | Cut -> Format.fprintf fmt "cut"
  | Check -> Format.fprintf fmt "check"
  | Thm -> Format.fprintf fmt "thm"


(** Logic type *)

type tlogic_type =
  | TPredicate of Ty.t list
  | TFunction of Ty.t list * Ty.t

(** Declarations *)

type 'a atdecl = ('a tdecl, 'a) annoted

and 'a tdecl =
  (* to simplify impl and extension of GUI, a TTtheory is seen a list
     of tdecl, although we only allow axioms in theories
     declarations *)
  | TTheory of
      Loc.t * string * Util.theories_extensions * ('a tdecl, 'a) annoted list
  | TAxiom of Loc.t * string * Util.axiom_kind * ('a tform, 'a) annoted
  | TRewriting of Loc.t * string * (('a tterm, 'a) annoted rwt_rule) list
  | TNegated_goal of Loc.t * goal_sort * string * ('a tform, 'a) annoted
  | TLogic of Loc.t * string list * tlogic_type
  | TPredicate_def of
      Loc.t * string *
      (string * Ty.t) list * ('a tform, 'a) annoted
  | TFunction_def of
      Loc.t * string *
      (string * Ty.t) list * Ty.t * ('a tform, 'a) annoted
  | TTypeDecl of Loc.t * Ty.t

(*****)

let string_of_op = function
  | OPand -> "and"
  | OPor -> "or"
  | OPimp -> "->"
  | OPiff -> "<->"
  | _ -> assert false

let print_binder fmt (s, t) =
  fprintf fmt "%a :%a" Symbols.print s Ty.print t

let print_binders fmt l =
  List.iter (fun c -> fprintf fmt "%a, " print_binder c) l

let rec print_term fmt t = match t.c.tt_desc with
  | TTconst Ttrue ->
    fprintf fmt "true"
  | TTconst Tfalse ->
    fprintf fmt "false"
  | TTconst Tvoid ->
    fprintf fmt "void"
  | TTconst (Tint n) ->
    fprintf fmt "%s" n
  | TTconst (Treal n) ->
    fprintf fmt "%s" (Num.string_of_num n)
  | TTconst Tbitv s ->
    fprintf fmt "%s" s
  | TTvar s ->
    fprintf fmt "%a" Symbols.print s
  | TTapp(s,l) ->
    fprintf fmt "%a(%a)" Symbols.print s print_term_list l
  | TTinfix(t1,s,t2) ->
    fprintf fmt "%a %a %a" print_term t1 Symbols.print s print_term t2
  | TTprefix (s, t') ->
    fprintf fmt "%a %a" Symbols.print s print_term t'
  | TTget (t1, t2) ->
    fprintf fmt "%a[%a]" print_term t1 print_term t2
  | TTset (t1, t2, t3) ->
    fprintf fmt "%a[%a<-%a]" print_term t1 print_term t2 print_term t3
  | TTextract (t1, t2, t3) ->
    fprintf fmt "%a^{%a,%a}" print_term t1 print_term t2 print_term t3
  | TTconcat (t1, t2) ->
    fprintf fmt "%a @ %a" print_term t1 print_term t2
  | TTdot (t1, s) ->
    fprintf fmt "%a.%s" print_term t1 (Hstring.view s)
  | TTrecord l ->
    fprintf fmt "{ ";
    List.iter
      (fun (s, t) -> fprintf fmt "%s = %a" (Hstring.view s) print_term t) l;
    fprintf fmt " }"
  | TTlet (binders, t2) ->
    fprintf fmt "let %a in %a" print_term_binders binders print_term t2
  | TTnamed (_, t) ->
    fprintf fmt "%a" print_term t

  | TTinInterval(e, i, j) ->
    fprintf fmt "%a in %a, %a"
      print_term e
      Symbols.print_bound i
      Symbols.print_bound j

  | TTmapsTo(x,e) ->
    fprintf fmt "%a |-> %a" Var.print x print_term e

  | TTite(cond, t1, t2) ->
    fprintf fmt "(if %a then %a else %a)"
      print_formula cond print_term t1 print_term t2
  | TTproject (grded, t1, s) ->
    fprintf fmt "%a#%s%s"
      print_term t1 (if grded then "" else "!") (Hstring.view s)

  | TTform f ->
    fprintf fmt "%a" print_formula f

  | TTmatch (e, cases) ->
    let pp_vars fmt l =
      match l with
        [] -> ()
      | [e,_,_] -> Var.print fmt e
      | (e,_,_) :: l ->
        fprintf fmt "(%a" Var.print e;
        List.iter (fun (e,_,_) -> fprintf fmt ", %a" Var.print e) l;
        fprintf fmt ")"
    in
    fprintf fmt "match %a with\n" print_term e;
    List.iter
      (fun (p, v) ->
         match p with
         | Constr {name = n; args = l} ->
           fprintf fmt "| %a %a -> %a\n" Hstring.print n pp_vars l print_term v
         | Var x ->
           fprintf fmt "| %a -> %a\n" Var.print x print_term v;
      )cases;
    fprintf fmt "end@."

and print_term_binders fmt l =
  match l with
  | [] -> assert false
  | (sy, t) :: l ->
    fprintf fmt "%a = %a" Symbols.print sy print_term t;
    List.iter (fun (sy, t) ->
        fprintf fmt ", %a = %a" Symbols.print sy print_term t) l

and print_term_list fmt = List.iter (fprintf fmt "%a," print_term)

and print_atom fmt a =
  match a.c with
  | TAtrue ->
    fprintf fmt "True"
  | TAfalse ->
    fprintf fmt "True"
  | TAeq [t1; t2] ->
    fprintf fmt "%a = %a" print_term t1 print_term t2
  | TAneq [t1; t2] ->
    fprintf fmt "%a <> %a" print_term t1 print_term t2
  | TAle [t1; t2] ->
    fprintf fmt "%a <= %a" print_term t1 print_term t2
  | TAlt [t1; t2] ->
    fprintf fmt "%a < %a" print_term t1 print_term t2
  | TApred (t, negated) ->
    if negated then fprintf fmt "(not (%a))" print_term t
    else print_term fmt t
  | TTisConstr (t1, s) ->
    fprintf fmt "%a ? %s" print_term t1 (Hstring.view s)
  | _ -> assert false

and print_triggers fmt l =
  List.iter (fun (tr, _) -> fprintf fmt "%a | " print_term_list tr) l

and print_formula fmt f =
  match f.c with
  | TFatom a ->
    print_atom fmt a
  | TFop(OPnot, [f]) ->
    fprintf fmt "not %a" print_formula f
  | TFop(OPif, [cond; f1;f2]) ->
    fprintf fmt "if %a then %a else %a"
      print_formula cond print_formula f1 print_formula f2
  | TFop(op, [f1; f2]) ->
    fprintf fmt "(%a %s %a)" print_formula f1 (string_of_op op) print_formula f2
  | TFop(op, l) ->
    fprintf fmt "(%a)" (
      Util.print_list_pp
        ~sep:(fun fmt () -> Format.fprintf fmt " %s " (string_of_op op))
        ~pp:print_formula) l
  | TFforall { qf_bvars = l; qf_triggers = t; qf_form = f; _ } ->
    fprintf fmt "forall %a [%a]. %a"
      print_binders l print_triggers t print_formula f
  | TFexists { qf_bvars = l; qf_triggers = t; qf_form = f; _ } ->
    fprintf fmt "exists %a [%a]. %a"
      print_binders l print_triggers t print_formula f
  | TFnamed (_, f') -> print_formula fmt f'

  | TFmatch (e, cases) ->
    let pp_vars fmt l =
      match l with
        [] -> ()
      | [e,_,_] -> Var.print fmt e
      | (e,_,_) :: l ->
        fprintf fmt "(%a" Var.print e;
        List.iter (fun (e,_,_) -> fprintf fmt ", %a" Var.print e) l;
        fprintf fmt ")"
    in
    fprintf fmt "match %a with\n" print_term e;
    List.iter
      (fun (p, v) ->
         match p with
         | Constr {name = n; args = l} ->
           fprintf fmt "| %a %a -> %a\n" Hstring.print n pp_vars l print_formula v
         | Var x ->
           fprintf fmt "| %a -> %a\n" Var.print x print_formula v;
      )cases;
    fprintf fmt "end@."

  | TFlet (_, binders, f) ->
    List.iter
      (fun (sy, let_e) ->
         fprintf fmt " let %a = " Symbols.print sy;
         match let_e with
         | TletTerm t -> fprintf fmt "%a in@." print_term t
         | TletForm f -> fprintf fmt "%a in@." print_formula f
      )binders;
    fprintf fmt "%a" print_formula f

(*
let rec print_tdecl fmt = function
  | TTheory (_, name, _, l) ->
    Format.fprintf fmt "th %s: @[<v>%a@]" name
      (Util.print_list_pp ~sep:Format.pp_print_space ~pp:print_atdecl) l
  | TAxiom (_, name, kind, f) ->
    Format.fprintf fmt "ax %s: @[<hov>%a@]" name print_formula f
  | TRewriting (_, name, l) ->
    Format.fprintf fmt "rwt %s: @[<hov>%a@]" name
      (Util.print_list_pp ~sep:Format.pp_print_space
         ~pp:(print_rwt print_term)) l
  | TGoal (_, sort, name, f) ->
    Format.fprintf fmt "goal %s: @[<hov>%a@]" name print_formula f

and print_atdecl fmt a = print_tdecl fmt a.c
*)

let fresh_hypothesis_name =
  let cpt = ref 0 in
  fun sort ->
    incr cpt;
    match sort with
    | Thm -> "@H"^(string_of_int !cpt)
    | _ -> "@L"^(string_of_int !cpt)

let is_local_hyp s =
  try Pervasives.(=) (String.sub s 0 2) "@L" with Invalid_argument _ -> false

let is_global_hyp s =
  try Pervasives.(=) (String.sub s 0 2) "@H" with Invalid_argument _ -> false


(* Monomorphization *)

let monomorphize_var (s,ty) = s, Ty.monomorphize ty

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
    | TTinInterval (e, lb, ub) ->
      TTinInterval(mono_term e, lb, ub)
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
    | TTlet (l,t2)->
      let l = List.rev_map (fun (x, t1) -> x, mono_term t1) (List.rev l) in
      TTlet (l, mono_term t2)
    | TTnamed (lbl, t)->
      TTnamed (lbl, mono_term t)
    | TTite (cond, t1, t2) ->
      TTite (monomorphize_form cond, mono_term t1, mono_term t2)

    | TTproject (grded, t, lbl) ->
      TTproject (grded, mono_term t, lbl)
    | TTmatch (e, pats) ->
      let e = mono_term e in
      let pats = List.rev_map (fun (p, f) -> p, mono_term f) (List.rev pats) in
      TTmatch (e, pats)

    | TTform f -> TTform (monomorphize_form f)

  in
  { c = {tt_ty = Ty.monomorphize tt_ty; tt_desc=tt_desc}; annot = id}

and monomorphize_term t = mono_term t

and monomorphize_atom tat =
  let c = match tat.c with
    | TAtrue | TAfalse -> tat.c
    | TAeq tl -> TAeq (List.map mono_term tl)
    | TAneq tl -> TAneq (List.map mono_term tl)
    | TAle tl -> TAle (List.map mono_term tl)
    | TAlt tl -> TAlt (List.map mono_term tl)
    | TAdistinct tl -> TAdistinct (List.map mono_term tl)
    | TApred (t, negated) -> TApred (mono_term t, negated)
    | TTisConstr (t, lbl) -> TTisConstr (mono_term t, lbl)
  in
  { tat with c = c }

and monomorphize_form tf =
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

    | TFlet (l, binders, tf) ->
      let l = List.map monomorphize_var l in
      let binders =
        List.rev_map
          (fun (sy, e) ->
             match e with
             | TletTerm tt -> sy, TletTerm (mono_term tt)
             | TletForm ff -> sy, TletForm (monomorphize_form ff)
          )(List.rev binders)
      in
      TFlet(l, binders, monomorphize_form tf)

    | TFnamed (hs,tf) ->
      TFnamed(hs, monomorphize_form tf)

    | TFmatch(e, pats) ->
      let e = mono_term e in
      let pats =
        List.rev_map
          (fun (p, f) -> p, monomorphize_form f) (List.rev pats)
      in
      TFmatch (e, pats)
  in
  { tf with c = c }



module Safe = struct

  (* Unified expressions.
     These are mainly there because alt-ergo distinguishes
     terms, atoms, and formulas, whereas some languages
     (and thus the typechecker) do not make this difference
     (for instance smtlib). Additionally, even though formulas
     can occur in terms (through the TTForm constructor),
     it is more convenient to have this wrapper in order
     to safely go from terms to formulas. *)
  type t =
    | Term of int atterm
    | Atom of int atatom
    | Form of int atform * Ty.tvar list
    (* Formulas also carry their set of explicitly
       quantified type variables, so that non top-level type
       variable quantification can be rejected as invalid. *)

  let print fmt = function
    | Term t -> print_term fmt t
    | Atom a -> print_atom fmt a
    | Form (f, []) -> print_formula fmt f
    | Form (f, l) ->
      Format.fprintf fmt "(%a) %a"
        (Util.print_list_pp
           ~sep:Format.pp_print_space ~pp:Ty.Safe.Var.print) l
        print_formula f

  let ty = function
    | Term { c = { tt_ty ; _ }; _ } -> tt_ty
    | Atom _
    | Form _ -> Ty.Safe.prop


  module Var = struct

    type t = {
      var : Symbols.t;
      ty  : Ty.t;
    }

    let hash { var; _ } = Symbols.hash var

    let compare v v' =
      Symbols.compare v.var v'.var

    let equal v v' = compare v v' = 0

    let print fmt { var; _ } =
      Format.fprintf fmt "%s" (Symbols.to_string var)

    let ty { ty; _ } = ty

    let make var ty = { var; ty; }

    let mk name ty = make (Symbols.var (Var.of_string name)) ty

  end

  module Const = struct

    type t = {
      symbol : Symbols.t;
      vars : Ty.Safe.Var.t list;
      args : Ty.t list;
      ret  : Ty.t;
    }

    let hash { symbol; _ } = Symbols.hash symbol

    let compare c c' =
      Symbols.compare c.symbol c'.symbol

    let equal c c' = compare c c' = 0

    let print fmt { symbol; _ } =
      Format.fprintf fmt "%s" (Symbols.to_string symbol)

    let print_ty fmt (vars, args, ret) =
      let rec aux_vars args ret fmt = function
        | [] -> aux_args ret fmt args
        | vars ->
          Format.fprintf fmt "%a ->@ %a"
            (Util.print_list_pp ~pp:Ty.Safe.Var.print
               ~sep:(fun fmt () -> Format.fprintf fmt " ->@ ")) vars
            (aux_args ret) args
      and aux_args ret fmt = function
        | [] -> Ty.print fmt ret
        | args ->
          Format.fprintf fmt "%a ->@ %a"
            (Util.print_list_pp ~pp:Ty.print
               ~sep:(fun fmt () -> Format.fprintf fmt " ->@ ")) args
            Ty.print ret
      in
      Format.fprintf fmt "@[<hov>%a@]" (aux_vars args ret) vars

    let print_full fmt c =
      Format.fprintf fmt "%a:@ %a" print c print_ty (c.vars, c.args, c.ret)

    let arity c =
      List.length c.vars,
      List.length c.args

    let make symbol vars args ret =
      { symbol; vars; args; ret; }

    let mk name vars args ret =
      make (Symbols.name name) vars args ret

    let tag _ _ _ = ()

    let name c = Symbols.to_string c.symbol

    let tlogic_type c =
      if Ty.Safe.equal Ty.Safe.prop c.ret
      then TPredicate c.args
      else TFunction (c.args, c.ret)

    let _true =
      make Symbols.True [] [] Ty.Safe.prop

    let _false =
      make Symbols.False [] [] Ty.Safe.prop

    module Int = struct
      let add =
        make Symbols.(Op Plus) [] [Ty.Safe.int; Ty.Safe.int] Ty.Safe.int

      let sub =
        make Symbols.(Op Minus) [] [Ty.Safe.int; Ty.Safe.int] Ty.Safe.int

      let mul =
        make Symbols.(Op Mult) [] [Ty.Safe.int; Ty.Safe.int] Ty.Safe.int

      let div =
        make Symbols.(Op Div) [] [Ty.Safe.int; Ty.Safe.int] Ty.Safe.int

      let modulo =
        make Symbols.(Op Modulo) [] [Ty.Safe.int; Ty.Safe.int] Ty.Safe.int

      let abs =
        make Symbols.(Op Abs_int) [] [Ty.Safe.int] Ty.Safe.int

      let lt =
        make Symbols.(Lit (L_built LT)) [] [Ty.Safe.int; Ty.Safe.int]
          Ty.Safe.prop

      let le =
        make Symbols.(Lit (L_built LE)) [] [Ty.Safe.int; Ty.Safe.int]
          Ty.Safe.prop

      let to_real =
        make Symbols.(Op Real_of_int) [] [Ty.Safe.int] Ty.Safe.real

    end

    module Real = struct
      let add =
        make Symbols.(Op Plus) [] [Ty.Safe.real; Ty.Safe.real] Ty.Safe.real

      let sub =
        make Symbols.(Op Minus) [] [Ty.Safe.real; Ty.Safe.real] Ty.Safe.real

      let mul =
        make Symbols.(Op Mult) [] [Ty.Safe.real; Ty.Safe.real] Ty.Safe.real

      let div =
        make Symbols.(Op Div) [] [Ty.Safe.real; Ty.Safe.real] Ty.Safe.real

      let lt =
        make Symbols.(Lit (L_built LT)) [] [Ty.Safe.real; Ty.Safe.real]
          Ty.Safe.prop

      let le =
        make Symbols.(Lit (L_built LE)) [] [Ty.Safe.real; Ty.Safe.real]
          Ty.Safe.prop

      let is_int =
        make Symbols.(Op Is_int) [] [Ty.Safe.real] Ty.Safe.prop

      let to_int =
        make Symbols.(Op Int_floor) [] [Ty.Safe.real] Ty.Safe.int

    end
  end

  exception Deep_type_quantification
  exception Wrong_type of t * Ty.t
  exception Wrong_arity of Const.t * int * int

  (* Auxiliary functions. *)

  let promote_term = function
    | Term { c = { tt_desc = TTform f; _ } ; _ } ->
      Form (f, [])
    | ((Term t) as e) when Ty.equal Ty.Safe.prop (ty e) ->
      Atom (mk (TApred (t, false)))
    | e -> e

  let promote_atom = function
    | Atom a -> Form (mk (TFatom a), [])
    | e -> e

  let expect_term = function
    | Term t -> t
    | Atom { c = TApred (t, false); _ } -> t
    | a ->
      begin match promote_atom a with
        | Form (f, []) ->
          mk { tt_desc = TTform f; tt_ty = Ty.Safe.prop; }
        | Form (_, _) ->
          raise Deep_type_quantification
        | _ -> assert false
      end

  let expect_prop t =
    match promote_atom @@ promote_term t with
    | Form (f, l) -> l, f
    | (Term _) as e ->
      raise (Wrong_type (e, Ty.Safe.prop))
    (* promote_atom guarantees this cannot happen *)
    | Atom _ -> assert false

    let expect_formula t =
      match expect_prop t with
      | [], f -> f
      | _ -> raise Deep_type_quantification

  (* Smart constructors:
     Wrappers to build term while checking the well-typedness *)
  let of_var v =
    Term (mk { tt_desc = TTvar v.Var.var; tt_ty = v.Var.ty })

  let _true = Atom (mk TAtrue)
  let _false = Atom (mk TAfalse)

  let mk_form_op op l =
    let l_f = List.map expect_formula l in
    Form (mk (TFop(op, l_f)), [])

  let neg t = mk_form_op OPnot [t]
  let imply p q = mk_form_op OPimp [p; q]
  let equiv p q = mk_form_op OPiff [p; q]
  let xor p q = mk_form_op OPxor [p; q]

  let match_builtin b args =
    let open Symbols in
    match b with
    | LE -> TAle args
    | LT -> TAlt args
    | IsConstr _ -> assert false

  let mk_atom l args =
    let open Symbols in
    match l with
    | L_eq -> Atom (mk (TAeq args))
    | L_built b ->
      (Atom (mk ((match_builtin b args))))
    | L_neg_eq -> Atom (mk (TAneq args))
    | L_neg_built b ->
      mk_form_op OPnot [Atom (mk ((match_builtin b args)))]

    | L_neg_pred -> match args with
      | [arg] -> Atom (mk (TApred(arg,true)))
      | _ -> assert false

  let apply c tys args =
    (* check arity *)
    let n_ty = List.length tys in
    let n_args = List.length args in
    let a_ty, a_args = Const.arity c in
    if n_ty <> a_ty || n_args <> a_args then
      raise (Wrong_arity (c, n_ty, n_args))
    else begin
      (* compute the type variable substitution *)
      let s = List.fold_left2 (fun acc v ty ->
          Ty.M.add v.Ty.v ty acc) Ty.M.empty c.Const.vars tys in
      (* comptue the actual expected arguments types *)
      let expected_args_ty = List.map (Ty.apply_subst s) c.Const.args in
      (* check that the arsg have the expected type, and unwrap them *)
      let actual_args =
        List.map2 (fun t expected_ty ->
            if not (Ty.equal (ty t) expected_ty) then
              raise (Wrong_type (t, expected_ty))
            else expect_term t
          ) args expected_args_ty in
      (* compute the return type and create the resulting term. *)
      let ret_ty = Ty.apply_subst s c.Const.ret in

      let open Symbols in
      match c.Const.symbol with
      | Lit l ->
        mk_atom l actual_args
      | _ ->
        promote_term (Term (
          mk ({ tt_ty = ret_ty;
                tt_desc = TTapp (c.Const.symbol, actual_args)})
        ))
    end

  (* Use a divide and conquer strategy to chain
     application of binary operators to a list of expressions. *)
  let mk_bin_op op l =
    let rec divide = function
      | [] -> []
      | [t] -> [t]
      | x :: y :: r ->
        let r' = divide r in
        let t = mk_form_op op [x; y] in
        t :: r'
    in
    let rec conquer = function
      | [] -> raise (Invalid_argument "Typed.mk_bin_op")
      | [t] -> t
      | l -> conquer (divide l)
    in
    conquer l

  let _and = mk_bin_op OPand
  let _or = mk_bin_op OPor

  (* TODO: allow real n-ary equalities.
     Currently, n-ary equalities are translated using a "star"
     of equalities (i.e. all elements of the chain are equal
     to the first), in order to avoid long chains that could
     be a problem for the union-find/congruence closure. *)
  let eqs = function
    | [] | [_] -> raise (Invalid_argument "Typed.eqs")
    | e :: r ->
      let e_ty = ty e in
      let e_t = expect_term e in
      let l = List.fold_left (fun acc e' ->
          if Ty.equal e_ty (ty e')
          then expect_term e' :: acc
          else raise (Wrong_type (e', e_ty))
        ) [] r in
      let l' = List.map (fun f_t -> Atom (mk (TAeq [e_t; f_t]))) l in
      _and l'

  let eq a b =
    let a_t = expect_term a in
    let b_t = expect_term b in
    let a_ty = a_t.c.tt_ty in
    let b_ty = b_t.c.tt_ty in
    if not (Ty.equal a_ty b_ty) then
      raise (Wrong_type (b, a_ty))
    else
      Atom (mk (TAeq [a_t; b_t]))

  let distinct = function
    | [] -> _true
    | x :: r ->
      let x_t = expect_term x in
      let expected_ty = x_t.c.tt_ty in
      let r' = List.map (fun t ->
          if not (Ty.equal expected_ty (ty t)) then
            raise (Wrong_type (t, expected_ty))
          else expect_term t
        ) r
      in
      Atom (mk (TAdistinct (x_t :: r')))

  (** free variable computation *)
  let add_fv (fv, bv) v ty =
    if Symbols.Set.mem v bv then fv
    else Symbols.Map.add v ty fv

  let rec fv_match f (fv, bv) = function
    | [] -> fv
    | (pattern, body) :: r ->
      let bv' = vars_of_pattern bv pattern in
      let fv' = f (fv, bv') body in
      fv_match f (fv', bv) r

  and vars_of_pattern s = function
    | Var v -> Symbols.Set.add (Symbols.var v) s
    | Constr { args; _ } ->
      List.fold_left (fun acc (v, _, _) ->
          Symbols.Set.add (Symbols.var v) acc) s args

  let rec fv_term_desc ty ((fv, bv) as acc) = function
    | TTconst _ -> fv
    | TTvar v -> add_fv acc v ty
    (* neither infix nor prefix operators cann be variables *)
    | TTinfix (l, _, r)             -> fv_term_list acc [l; r]
    | TTprefix (_, t)               -> fv_term acc t
    | TTapp (_, l)                  -> fv_term_list acc l
    | TTmapsTo (_, t)               -> fv_term acc t
    | TTinInterval (t, l, u)        -> fv_term_bounds acc t l u
    | TTget (a, i)                  -> fv_term_list acc [a; i]
    | TTset (a, i, v)               -> fv_term_list acc [a; i; v]
    | TTextract (a, i, l)           -> fv_term_list acc [a; i; l]
    | TTconcat (u, v)               -> fv_term_list acc [u; v]
    | TTdot (t, _)                  -> fv_term acc t
    | TTrecord l                    -> fv_term_list acc (List.map snd l)
    | TTnamed (_, t)                -> fv_term acc t
    | TTite (f, a, b)               -> fv_term_list ((fv_form acc f), bv) [a; b]
    | TTlet (l, body)               -> fv_term_let acc body l
    | TTproject (_, t, _)           -> fv_term acc t
    | TTmatch (e, l)                -> fv_term_match ((fv_term acc e), bv) l
    | TTform f                      -> fv_form acc f

  and fv_term_match acc l = fv_match fv_term acc l

  and fv_term_bound ((fv, _) as acc) = function
    | { Symbols.kind = Symbols.VarBnd v; sort; _ } ->
      add_fv acc (Symbols.var v) sort
    | _ -> fv

  and fv_term_bounds ((_, bv) as acc) t l u =
    let fv' = fv_term_bound acc l in
    let fv'' = fv_term_bound (fv', bv) u in
    fv_term (fv'', bv) t

  and fv_term_let ((_, bv) as acc) body = function
    | [] -> fv_term acc body
    | (x, t) :: r ->
      let fv' = fv_term acc t in
      let bv' = Symbols.Set.add x bv in
      fv_term_let (fv', bv') body r

  and fv_term_list (fv, bv) l =
    let aux lv t = fv_term (lv, bv) t in
    List.fold_left aux fv l

  and fv_term acc t =
    fv_term_desc t.c.tt_ty acc t.c.tt_desc

  and fv_atom_desc ((fv, _) as acc) = function
    | TAtrue | TAfalse -> fv
    | TAeq l | TAneq l
    | TAle l | TAlt l
    | TAdistinct l -> fv_term_list acc l
    | TApred (t, _) -> fv_term acc t
    | TTisConstr (t, _) -> fv_term acc t

  and fv_atom acc a =
    fv_atom_desc acc a.c

  and fv_form_desc ((fv, bv) as acc) = function
    | TFatom a -> fv_atom acc a
    | TFop (_, l) -> fv_form_list acc l
    | TFforall q | TFexists q ->
      let aux m (v, ty) = Symbols.Map.add v ty m in
      List.fold_left aux fv q.qf_upvars
    | TFnamed (_, f) -> fv_form acc f
    | TFlet (l, _, _) ->
      let aux m (v, ty) = Symbols.Map.add v ty m in
      List.fold_left aux fv l
    | TFmatch (e, l) ->
      fv_form_match (fv_term acc e, bv) l

  and fv_form_match acc l = fv_match fv_form acc l

  and fv_form_let ((_, bv) as acc) body = function
    | [] -> fv_form acc body
    | (v, TletTerm t) :: r ->
      let fv' = fv_term acc t in
      let bv' = Symbols.Set.add v bv in
      fv_form_let (fv', bv') body r
    | (v, TletForm f) :: r ->
      let fv' = fv_form acc f in
      let bv' = Symbols.Set.add v bv in
      fv_form_let (fv', bv') body r

  and fv_form_list (fv, bv) l =
    let aux lv t = fv_form (lv, bv) t in
    List.fold_left aux fv l

  and fv_form acc f =
    fv_form_desc acc f.c

  let _empty_acc = (Symbols.Map.empty, Symbols.Set.empty)

  (* NOTE: free type variables are not computed here. *)
  let to_fv m =
    [], Symbols.Map.fold (fun v ty acc ->
        Var.make v ty :: acc) m []

  let fv = function
    | Term t -> to_fv @@ fv_term _empty_acc t
    | Atom a -> to_fv @@ fv_atom _empty_acc a
    | Form (f, _) -> to_fv @@ fv_form _empty_acc f

  let var_to_tuple { Var.var; ty; } = var, ty

  let all (_, t_fv) (ty_qv, t_qv) e =
    let f = expect_formula e in
    let qf_bvars = List.map var_to_tuple t_qv in
    let qf_upvars = List.map var_to_tuple t_fv in
    Form (mk @@ TFforall {
        qf_bvars; qf_upvars;
        qf_triggers = [];
        qf_hyp = [];
        qf_form = f;
      }, ty_qv)

  let ex (_, t_fv) (ty_qv, t_qv) e =
    let f = expect_formula e in
    let qf_bvars = List.map var_to_tuple t_qv in
    let qf_upvars = List.map var_to_tuple t_fv in
    Form (mk @@ TFexists {
        qf_bvars; qf_upvars;
        qf_triggers = [];
        qf_hyp = [];
        qf_form = f;
      }, ty_qv)

  let letin l e =
    match promote_atom e with
    | Atom _ -> assert false
    | Term t ->
      let l' = List.map (fun (v, e') ->
          if not (Ty.equal v.Var.ty (ty e')) then
            raise (Wrong_type (e, v.Var.ty))
          else
            v.Var.var, expect_term e'
        ) l in
      Term (mk @@ { tt_desc = TTlet (l', t); tt_ty = t.c.tt_ty})
    | Form (f, []) ->
      let l' = List.map (fun (v, e') ->
          match promote_atom e' with
          | Term t' -> v.Var.var, TletTerm t'
          | Form (f', []) -> v.Var.var, TletForm f'
          | Form (_, _) -> raise Deep_type_quantification
          | Atom _ -> assert false
        ) l in
      let fv_m = fv_form_let _empty_acc f l' in
      let fv_l = Symbols.Map.fold (fun v ty acc -> (v, ty) :: acc) fv_m [] in
      Form (mk @@ TFlet (fv_l, l', f), [])
    | Form (_, _) -> raise Deep_type_quantification

  (* Integers *)
  let int s : t =
    Term (mk { tt_ty = Ty.Safe.int;
               tt_desc = TTconst (Tint s); })

  let real s : t =
    let s = begin match String.split_on_char '.' s with
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
    in
    Term (mk { tt_ty = Ty.Safe.real; tt_desc = TTconst (Treal s); })

  (* Array operations *)
  let get_array_type arr =
    match ty arr with
    | Ty.Tfarray (src, dst) -> (src, dst)
    | _ ->
      let a_ty = Ty.Safe.of_var (Ty.Safe.Var.mk "a") in
      let b_ty = Ty.Safe.of_var (Ty.Safe.Var.mk "b") in
      let gen_arr_ty = Ty.Safe.array a_ty b_ty in
      raise (Wrong_type (arr, gen_arr_ty))

  let select arr idx =
    let idx_ty = ty idx in
    let (src, dst) = get_array_type arr in
    if Ty.equal idx_ty src then
      Term (mk { tt_ty = dst;
                 tt_desc =  TTget (expect_term arr,
                                   expect_term idx) })
    else
      raise (Wrong_type (idx, src))

  let store arr idx value =
    let idx_ty = ty idx in
    let val_ty = ty value in
    let (src, dst) = get_array_type arr in
    if Ty.equal idx_ty src then
      if Ty.equal val_ty dst then
        Term (mk { tt_ty = ty arr;
                   tt_desc =  TTset (expect_term arr,
                                     expect_term idx,
                                     expect_term value) })
      else
        raise (Wrong_type (value, dst))
    else
      raise (Wrong_type (idx, src))

  (* conditionals *)
  let ite c a b =
    let cond = expect_formula c in
    if not (Ty.equal (ty a) (ty b)) then
      raise (Wrong_type (b, ty a))
    else begin
      let a_t = expect_term a in
      let b_t = expect_term b in
      Term (mk { tt_ty = ty a;
                 tt_desc = TTite (cond, a_t, b_t); })
    end

  (* bitvectors *)
  let get_bitv_size t =
    match ty t with
    | (Ty.Tbitv n) as t_ty -> t_ty, n
    | _ -> raise (Wrong_type (t, Ty.Safe.bitv (-1)))

  let mk_bitv s =
    let n = String.length s in
    Term (mk { tt_ty = Ty.Safe.bitv n;
               tt_desc = TTconst (Tbitv s); })

  let bitv_concat s t =
    let _, n = get_bitv_size s in
    let _, m = get_bitv_size t in
    Term (mk { tt_ty = Ty.Safe.bitv (n + m);
               tt_desc = TTconcat (expect_term s, expect_term t); } )

  let bitv_extract i j t =
    let _, m = get_bitv_size t in
    if j < 0 || i > m then
      raise (Invalid_argument "Typed.bitv_extract")
    else begin
      let n = i - j + 1 in
      let t_t = expect_term t in
      let i_t = expect_term @@ int (string_of_int i) in
      let j_t = expect_term @@ int (string_of_int j) in
      Term (mk { tt_ty = Ty.Safe.bitv n;
                 tt_desc = TTextract(t_t, j_t, i_t); })
    end

  let rec bitv_repeat i t =
    if i <= 1 then t
    else begin
      let t' = bitv_repeat (i / 2) t in
      if i mod 2 = 0 then bitv_concat t' t'
      else bitv_concat t (bitv_concat t' t')
    end

  (* TODO: implement builtins for these bitvector operations ? *)
  let bitv_extend s = fun i t ->
    let _, n = get_bitv_size t in
    let t_t = expect_term t in
    let i_t = expect_term @@ int (string_of_int i) in
    Term (mk { tt_ty = Ty.Safe.bitv (n + i); tt_desc = TTapp (s, [i_t; t_t]); })

  let bitv_rotate s = fun i t ->
    let tt_ty, _ = get_bitv_size t in
    let i_t = expect_term @@ int (string_of_int i) in
    Term (mk { tt_ty; tt_desc = TTapp (s, [i_t; expect_term t]); })

  let bitv_unary s = fun t ->
    let tt_ty, _ = get_bitv_size t in
    Term (mk { tt_ty; tt_desc = TTapp (s, [expect_term t]); })

  let bitv_binary symb = fun s t ->
    let tt_ty, n = get_bitv_size s in
    let _, m = get_bitv_size t in
    if n <> m then
      raise (Wrong_type (t, tt_ty))
    else begin
      Term (mk { tt_ty; tt_desc = TTapp (symb, [expect_term s; expect_term t]); })
    end

  let bitv_binary_pred symb = fun s t ->
    let bv_ty, n = get_bitv_size s in
    let _, m = get_bitv_size t in
    if n <> m then
      raise (Wrong_type (t, bv_ty))
    else begin
      Term (mk { tt_ty = Ty.Safe.prop;
                 tt_desc = TTapp (symb, [expect_term s; expect_term t]); })
    end

  let zero_extend = bitv_extend (Symbols.name "zero_extend")
  let sign_extend = bitv_extend (Symbols.name "sign_extend")
  let rotate_left = bitv_rotate (Symbols.name "rotate_left")
  let rotate_right = bitv_rotate (Symbols.name "rotate_right")

  let bvnot = bitv_unary (Symbols.name "bvnot")
  let bvand = bitv_binary (Symbols.name "bvand")
  let bvor = bitv_binary (Symbols.name "bvor")
  let bvnand = bitv_binary (Symbols.name "bvnand")
  let bvnor = bitv_binary (Symbols.name "bvnor")
  let bvxor = bitv_binary (Symbols.name "bvxor")
  let bvxnor = bitv_binary (Symbols.name "bvxnor")
  let bvcomp = bitv_binary_pred (Symbols.name "bvcomp")

  let bvneg = bitv_unary (Symbols.name "bvneg")
  let bvadd = bitv_binary (Symbols.name "bvadd")
  let bvsub = bitv_binary (Symbols.name "bvsub")
  let bvmul = bitv_binary (Symbols.name "bvmul")
  let bvudiv = bitv_binary (Symbols.name "bvudiv")
  let bvurem = bitv_binary (Symbols.name "bvurem")
  let bvsdiv = bitv_binary (Symbols.name "bvsdiv")
  let bvsrem = bitv_binary (Symbols.name "bvsrem")
  let bvsmod = bitv_binary (Symbols.name "bvsmod")

  let bvshl = bitv_binary (Symbols.name "bvshl")
  let bvlshr = bitv_binary (Symbols.name "bvlshr")
  let bvashr = bitv_binary (Symbols.name "bvashr")

  let bvult = bitv_binary_pred (Symbols.name "bvult")
  let bvule = bitv_binary_pred (Symbols.name "bvule")
  let bvugt = bitv_binary_pred (Symbols.name "bvugt")
  let bvuge = bitv_binary_pred (Symbols.name "bvuge")
  let bvslt = bitv_binary_pred (Symbols.name "bvslt")
  let bvsle = bitv_binary_pred (Symbols.name "bvsle")
  let bvsgt = bitv_binary_pred (Symbols.name "bvsgt")
  let bvsge = bitv_binary_pred (Symbols.name "bvsge")

  (* Arithmetic integers *)
  module Int = struct
    type nonrec t = t
    let int s = int s
    let neg i = apply Const.Int.sub [] [int "0";i]
    let add i j = apply Const.Int.add [] [i;j]
    let sub i j = apply Const.Int.sub [] [i;j]
    let mul i j = apply Const.Int.mul [] [i;j]
    let div i j = apply Const.Int.div [] [i;j]
    let modulo i j = apply Const.Int.modulo [] [i;j]
    let abs i = apply Const.Int.abs [] [i;]
    let lt i j = apply Const.Int.lt [] [i;j]
    let le i j = apply Const.Int.le [] [i;j]
    let gt i j = apply Const.Int.lt [] [j;i]
    let ge i j = apply Const.Int.le [] [j;i]
    let divisible i j =
      let n = apply Const.Int.modulo [] [int i;j] in
      let zero = int "0" in
      let f = Const.make Symbols.(Lit L_eq) [] [Ty.Safe.int; Ty.Safe.int]
        Ty.Safe.prop
      in
      apply f [] [n;zero]
  end

  (* Arithmetic reals *)
  module Real = struct
    type nonrec t = t
    let real s = real s
    let neg i = apply Const.Real.sub [] [real "0";i]
    let add i j = apply Const.Real.add [] [i;j]
    let sub i j = apply Const.Real.sub [] [i;j]
    let mul i j = apply Const.Real.mul [] [i;j]
    let div i j = apply Const.Real.div [] [i;j]
    let lt i j = apply Const.Real.lt [] [i;j]
    let le i j = apply Const.Real.le [] [i;j]
    let gt i j = apply Const.Real.lt [] [j;i]
    let ge i j = apply Const.Real.le [] [j;i]
  end

  (* Arithmetic reals and integers *)
  module Real_Int = struct
    type nonrec t = t
    type ty = Ty.t

    let ty t = ty t

    let int s = int s
    let real s = real s

    module Int = struct
      include Int
      let to_real i = apply Const.Int.to_real [] [i]
    end

    module Real = struct
      include Real
      let is_int i = apply Const.Real.is_int [] [i]

      let to_int i = apply Const.Real.to_int [] [i]
    end
  end

  (* for compatibility purposes with dolmen *)
  let tag _ _ _ = ()

end
