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
  | TTinfix of 'a atterm * Symbols.t * 'a atterm
  | TTprefix of Symbols.t * 'a atterm
  | TTapp of Symbols.t * 'a atterm list
  | TTmapsTo of Var.t * 'a atterm
  | TTinInterval of 'a atterm * Symbols.bound * Symbols.bound
  (* bool = true <-> interval is_open *)

  | TTget of 'a atterm * 'a atterm
  | TTset of
      'a atterm * 'a atterm * 'a atterm
  | TTextract of
      'a atterm * 'a atterm * 'a atterm
  | TTconcat of 'a atterm * 'a atterm
  | TTdot of 'a atterm * Hstring.t
  | TTrecord of (Hstring.t * 'a atterm) list
  | TTlet of (Symbols.t * 'a atterm) list * 'a atterm
  | TTnamed of Hstring.t * 'a atterm
  | TTite of 'a atform *
             'a atterm * 'a atterm
  | TTproject of bool * 'a atterm  * Hstring.t
  | TTmatch of 'a atterm * (pattern * 'a atterm) list
  | TTform of 'a atform

and 'a atatom = ('a tatom, 'a) annoted

and 'a tatom =
  | TAtrue
  | TAfalse
  | TAeq of 'a atterm list
  | TAdistinct of 'a atterm list
  | TAneq of 'a atterm list
  | TAle of 'a atterm list
  | TAlt of 'a atterm list
  | TApred of 'a atterm * bool (* true <-> negated *)
  | TTisConstr of 'a atterm  * Hstring.t

and 'a quant_form = {
  (* quantified variables that appear in the formula *)
  qf_bvars : (Symbols.t * Ty.t) list ;
  qf_upvars : (Symbols.t * Ty.t) list ;
  qf_triggers : ('a atterm list * bool) list ;
  qf_hyp : 'a atform list;
  qf_form : 'a atform
}

and 'a atform = ('a tform, 'a) annoted

and 'a tform =
  | TFatom of 'a atatom
  | TFop of oplogic * ('a atform) list
  | TFforall of 'a quant_form
  | TFexists of 'a quant_form
  | TFlet of (Symbols.t * Ty.t) list *
             (Symbols.t * 'a tlet_kind) list * 'a atform
  | TFnamed of Hstring.t * 'a atform
  | TFmatch of 'a atterm * (pattern * 'a atform) list

and 'a tlet_kind =
  | TletTerm of 'a atterm
  | TletForm of 'a atform

(** Toplevel common components *)

let true_atatom     = {c=TAtrue; annot = new_id ()}
let false_atatom    = {c=TAfalse; annot = new_id ()}

let true_tform      = TFatom true_atatom
let false_tform     = TFatom false_atatom

let true_atform  = {c = true_tform; annot = new_id()}
let false_atform = {c = false_tform; annot = new_id()}

let true_term    = {tt_desc = TTconst Ttrue; tt_ty=Ty.Tbool}
let false_term   = {tt_desc = TTconst Tfalse; tt_ty=Ty.Tbool}

let true_atterm  = {c = true_term; annot = new_id ()}
let false_atterm = {c = false_term; annot = new_id ()}

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
  | TAxiom of Loc.t * string * Util.axiom_kind * 'a atform
  | TRewriting of Loc.t * string * ('a atterm rwt_rule) list
  | TGoal of Loc.t * goal_sort * string * 'a atform
  | TLogic of Loc.t * string list * tlogic_type
  | TPredicate_def of
      Loc.t * string *
      (string * Ty.t) list * 'a atform
  | TFunction_def of
      Loc.t * string *
      (string * Ty.t) list * Ty.t * 'a atform
  | TTypeDecl of Loc.t * Ty.t
  | TPush of Loc.t * int
  | TPop of Loc.t * int

let eq_tconstant (c1 : tconstant) (c2 : tconstant) : bool =
  match c1, c2 with
    Tint s1, Tint s2
  | Tbitv s1, Tbitv s2 -> String.equal s1 s2
  | Treal n1, Treal n2 -> Num.eq_num n1 n2
  | Ttrue, Ttrue | Tfalse, Tfalse | Tvoid, Tvoid -> true
  | _ -> false

let eq_pattern (p1 : pattern) (p2 : pattern) : bool =
  match p1, p2 with
    Constr {name = name1; args = args1},
    Constr {name = name2; args = args2} ->
    Hstring.equal name1 name2
    &&
    Util.eq_list
      (fun (x1,s1,t1) (x2,s2,t2) ->
         Var.equal x1 x2 &&
         Hstring.equal s1 s2 &&
         Ty.equal t1 t2)
      args1
      args2

  | Var x1, Var x2 -> Var.equal x1 x2
  | _,_ -> false

let rec eq_tterm (t1 : 'a tterm) (t2 : 'a tterm) : bool =
  Ty.equal t1.tt_ty t2.tt_ty && eq_tt_desc t1.tt_desc t2.tt_desc

and eq_tt_desc (e1 : 'a tt_desc) (e2 : 'a tt_desc) : bool =
  match e1, e2 with
    TTconst c1, TTconst c2 -> eq_tconstant c1 c2
  | TTvar v1, TTvar v2 -> Symbols.equal v1 v2
  | TTinfix (t11, symb1, t12), TTinfix (t21, symb2, t22) ->
    Symbols.equal symb1 symb2 &&
    eq_tterm t11.c t21.c &&
    eq_tterm t12.c t22.c

  | TTprefix (s1,t1), TTprefix (s2, t2) ->
    Symbols.equal s1 s2 &&
    eq_tterm t1.c t2.c

  | TTapp (s1, l1), TTapp (s2, l2) ->
    Symbols.equal s1 s2 &&
    Util.eq_list
      (fun t1 t2 -> eq_tterm t1.c t2.c)
      l1 l2

  | TTmapsTo (x1, t1), TTmapsTo (x2, t2) ->
    Var.equal x1 x2 &&
    eq_tterm t1.c t2.c

  | TTget (t11, t12), TTget (t21, t22)
  | TTconcat (t11, t12), TTconcat (t21, t22) ->
    eq_tterm t11.c t21.c &&
    eq_tterm t12.c t22.c

  | TTset (t11, t12, t13), TTset (t21, t22, t23)
  | TTextract (t11, t12, t13), TTextract (t21, t22, t23)  ->
    eq_tterm t11.c t21.c &&
    eq_tterm t12.c t22.c &&
    eq_tterm t13.c t23.c

  | TTdot (t1, s1), TTdot (t2, s2)
  | TTnamed (s1, t1), TTnamed (s2, t2) ->
    Hstring.equal s1 s2 &&
    eq_tterm t1.c t2.c

  | TTrecord l1, TTrecord l2 ->
    Util.eq_list
      (fun  (s1,t1) (s2,t2) -> Hstring.equal s1 s2 && eq_tterm t1.c t2.c)
      l1 l2

  | TTlet (l1, t1), TTlet (l2, t2) ->
    eq_tterm t1.c t2.c &&
    Util.eq_list
      (fun (s1, t1) (s2, t2) ->
         Symbols.equal s1 s2 && eq_tterm t1.c t2.c)
      l1
      l2

  | TTite (c1,th1,el1), TTite (c2,th2,el2) ->
    eq_tform c1.c c2.c && eq_tterm th1.c th2.c && eq_tterm el1.c el2.c

  | TTproject (b1,t1,s1), TTproject (b2,t2,s2) ->
    (b1 && (not b2) || (not b1) && b2)
    && eq_tterm t1.c t2.c && Hstring.equal s1 s2

  | TTmatch (t1, l1), TTmatch (t2, l2) ->
    eq_tterm t1.c t2.c &&
    Util.eq_list
      (fun (p1,t1) (p2,t2) ->
         eq_pattern p1 p2 && eq_tterm t1.c t2.c
      )
      l1
      l2

  | TTform f1, TTform f2 -> eq_tform f1.c f2.c
  | _,_ -> false

and eq_tatom (a1 : 'a tatom) (a2 : 'a tatom) : bool =
  match a1, a2 with
    TAtrue, TAtrue
  | TAfalse, TAfalse -> true
  | TAeq l1, TAeq l2
  | TAdistinct l1, TAdistinct l2
  | TAneq l1, TAneq l2
  | TAle l1, TAle l2
  | TAlt l1, TAlt l2 ->
    Util.eq_list
      (fun t1 t2 -> eq_tterm t1.c t2.c)
      l1
      l2
  | TApred (t1, b1), TApred (t2, b2) ->
    (b1 && (not b2) || (not b1) && b2) &&
    eq_tterm t1.c t2.c
  | TTisConstr (t1, s1), TTisConstr (t2, s2) ->
    Hstring.equal s1 s2 && eq_tterm t1.c t2.c
  | _,_ -> false

and eq_quant_form (q1 : 'a quant_form) (q2 : 'a quant_form) : bool =
  let stylist =
    Util.eq_list
      (fun (s1,t1) (s2, t2) -> Symbols.equal s1 s2 && Ty.equal t1 t2)
  in
  stylist q1.qf_bvars q2.qf_bvars &&
  stylist q1.qf_upvars q2.qf_upvars &&
  Util.eq_list (fun f1 f2 -> eq_tform f1.c f2.c) q1.qf_hyp q2.qf_hyp &&
  eq_tform q1.qf_form.c q2.qf_form.c &&
  Util.eq_list
    (fun (tlist1,b1) (tlist2,b2) ->
       (b1 && (not b2) || (not b1) && b2) &&
       Util.eq_list
         (fun t1 t2 -> eq_tterm t1.c t2.c)
         tlist1
         tlist2)
    q1.qf_triggers
    q2.qf_triggers

and eq_tform (f1 : 'a tform) (f2 : 'a tform) : bool =
  match f1, f2 with
  | TFatom a1, TFatom a2 -> eq_tatom a1.c a2.c

  | TFop (op1, l1), TFop (op2, l2) ->
    (Stdlib.(=)) op1 op2 &&
    Util.eq_list
      (fun f1 f2 -> eq_tform f1.c f2.c)
      l1
      l2

  | TFforall q1, TFforall q2
  | TFexists q1, TFexists q2 ->
    eq_quant_form q1 q2

  | TFlet (stlist1, slklist1,f1), TFlet (stlist2, slklist2,f2) ->
    let stylist =
      Util.eq_list
        (fun (s1,t1) (s2, t2) -> Symbols.equal s1 s2 && Ty.equal t1 t2)
    in
    stylist stlist1 stlist2 &&
    Util.eq_list
      (fun (s1,lf1) (s2, lf2) -> Symbols.equal s1 s2 && eq_tlet_kind lf1 lf2)
      slklist1 slklist2
    &&
    eq_tform f1.c f2.c

  | TFnamed (s1, f1), TFnamed (s2, f2) ->
    Hstring.equal s1 s2 && eq_tform f1.c f2.c

  | TFmatch (t1, pfl1), TFmatch (t2, pfl2) ->
    eq_tterm t1.c t2.c &&
    Util.eq_list
      (fun (p1, f1) (p2, f2) -> eq_pattern p1 p2 && eq_tform f1.c f2.c)
      pfl1
      pfl2

  | _,_ -> false

and eq_tlet_kind (k1 : 'a tlet_kind) (k2 : 'a tlet_kind) : bool =
  match k1, k2 with
    TletTerm t1, TletTerm t2 -> eq_tterm t1.c t2.c
  | TletForm f1, TletForm f2 -> eq_tform f1.c f2.c
  | _,_ -> false

(*****)

let string_of_op = function
  | OPand -> "and"
  | OPor -> "or"
  | OPimp -> "->"
  | OPiff -> "<->"
  | OPxor -> "xor"
  | OPif -> "ite"
  | _ -> assert false

type 'annot annot_printer = Format.formatter -> 'annot -> unit
type ('a,'annot) annoted_printer =
  Format.formatter -> ('a,'annot) annoted -> unit

let (no_print : _ annot_printer) = fun fmt _ -> fprintf fmt ""
let (int_print : int annot_printer) = fun fmt -> fprintf fmt ".%i"

let print_annot
    (pp_annot : 'annot annot_printer)
    (print : ('a,'annot) annoted_printer)
    (fmt : Format.formatter) (t : ('a, 'annot) annoted) =
  fprintf fmt "%a%a" print t pp_annot t.annot

let print_binder fmt (s, t) =
  fprintf fmt "%a :%a" Symbols.print s Ty.print t

let print_binders fmt l =
  List.iter (fun c -> fprintf fmt "%a, " print_binder c) l

let rec print_term ?(annot=no_print) fmt t =
  let printer fmt t =
    match t.c.tt_desc with
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
      fprintf fmt "%a(%a)" Symbols.print s (print_term_list ~annot) l
    | TTinfix(t1,s,t2) ->
      fprintf
        fmt
        "%a %a %a"
        (print_term ~annot) t1
        Symbols.print s
        (print_term ~annot) t2
    | TTprefix (s, t') ->
      fprintf fmt "%a %a" Symbols.print s (print_term ~annot) t'
    | TTget (t1, t2) ->
      fprintf fmt "%a[%a]" (print_term ~annot) t1 (print_term ~annot) t2
    | TTset (t1, t2, t3) ->
      fprintf
        fmt
        "%a[%a<-%a]"
        (print_term ~annot) t1
        (print_term ~annot) t2
        (print_term ~annot) t3
    | TTextract (t1, t2, t3) ->
      fprintf
        fmt
        "%a^{%a,%a}"
        (print_term ~annot) t1
        (print_term ~annot) t2
        (print_term ~annot) t3
    | TTconcat (t1, t2) ->
      fprintf fmt "%a @ %a" (print_term ~annot) t1 (print_term ~annot) t2
    | TTdot (t1, s) ->
      fprintf fmt "%a.%s" (print_term ~annot) t1 (Hstring.view s)
    | TTrecord l ->
      fprintf fmt "{ ";
      List.iter
        (fun (s, t) ->
           fprintf fmt "%s = %a" (Hstring.view s) (print_term ~annot) t) l;
      fprintf fmt " }"
    | TTlet (binders, t2) ->
      fprintf
        fmt
        "let %a in %a"
        (print_term_binders ~annot) binders
        (print_term ~annot) t2
    | TTnamed (_, t) ->
      fprintf fmt "%a" (print_term ~annot) t

    | TTinInterval(e, i, j) ->
      fprintf fmt "%a in %a, %a"
        (print_term ~annot) e
        Symbols.print_bound i
        Symbols.print_bound j

    | TTmapsTo(x,e) ->
      fprintf fmt "%a |-> %a" Var.print x (print_term ~annot) e

    | TTite(cond, t1, t2) ->
      fprintf fmt "(if %a then %a else %a)"
        (print_formula ~annot) cond
        (print_term ~annot) t1
        (print_term ~annot) t2
    | TTproject (grded, t1, s) ->
      fprintf fmt "%a#%s%s"
        (print_term ~annot) t1 (if grded then "" else "!") (Hstring.view s)

    | TTform f ->
      fprintf fmt "%a" (print_formula ~annot) f

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
      fprintf fmt "match %a with\n" (print_term ~annot) e;
      List.iter
        (fun (p, v) ->
           match p with
           | Constr {name = n; args = l} ->
             fprintf
               fmt
               "| %a %a -> %a\n"
               Hstring.print n
               pp_vars l
               (print_term ~annot) v
           | Var x ->
             fprintf fmt "| %a -> %a\n" Var.print x (print_term ~annot) v;
        )cases;
      fprintf fmt "end@."
  in
  print_annot annot printer fmt t

and print_term_binders ?(annot=no_print) fmt l =
  match l with
  | [] -> assert false
  | (sy, t) :: l ->
    fprintf fmt "%a = %a" Symbols.print sy (print_term ~annot) t;
    List.iter (fun (sy, t) ->
        fprintf fmt ", %a = %a" Symbols.print sy (print_term ~annot) t) l

and print_term_list ?(annot=no_print) fmt = List.iter (fprintf fmt "%a," (print_term ~annot))

and print_atom ?(annot=no_print) fmt a =
  match a.c with
  | TAtrue ->
    fprintf fmt "True"
  | TAfalse ->
    fprintf fmt "True"
  | TAeq [t1; t2] ->
    fprintf fmt "%a = %a" (print_term ~annot) t1 (print_term ~annot) t2
  | TAneq [t1; t2] ->
    fprintf fmt "%a <> %a" (print_term ~annot) t1 (print_term ~annot) t2
  | TAle [t1; t2] ->
    fprintf fmt "%a <= %a" (print_term ~annot) t1 (print_term ~annot) t2
  | TAlt [t1; t2] ->
    fprintf fmt "%a < %a" (print_term ~annot) t1 (print_term ~annot) t2
  | TApred (t, negated) ->
    if negated then fprintf fmt "(not (%a))" (print_term ~annot) t
    else (print_term ~annot) fmt t
  | TTisConstr (t1, s) ->
    fprintf fmt "%a ? %s" (print_term ~annot) t1 (Hstring.view s)
  | TAdistinct l ->
    fprintf fmt "distinct(%a)" (print_term_list ~annot) l
  | _ -> assert false

and print_triggers ?(annot=no_print) fmt l =
  List.iter (fun (tr, _) -> fprintf fmt "%a | " (print_term_list ~annot) tr) l

and print_formula ?(annot=no_print) fmt f =
  match f.c with
  | TFatom a ->
    print_atom fmt a
  | TFop(OPnot, [f]) ->
    fprintf fmt "not %a" (print_formula ~annot) f
  | TFop(OPif, [cond; f1;f2]) ->
    fprintf fmt "if %a then %a else %a"
      (print_formula ~annot) cond (print_formula ~annot) f1 (print_formula ~annot) f2
  | TFop(op, [f1; f2]) ->
    fprintf fmt "%a %s %a" (print_formula ~annot) f1 (string_of_op op) (print_formula ~annot) f2
  | TFforall { qf_bvars = l; qf_triggers = t; qf_form = f; _ } ->
    fprintf fmt "forall %a [%a]. %a"
      print_binders l (print_triggers ~annot) t (print_formula ~annot) f

  | TFlet (_, binders, f) ->
    List.iter
      (fun (sy, let_e) ->
         fprintf fmt " let %a = " Symbols.print sy;
         match let_e with
         | TletTerm t -> fprintf fmt "%a in@." (print_term ~annot) t
         | TletForm f -> fprintf fmt "%a in@." (print_formula ~annot) f
      )binders;
    fprintf fmt "%a" (print_formula ~annot) f
  | _ -> fprintf fmt "(formula pprint not implemented)"

(*
let rec print_tdecl fmt = function

  | TTheory (_, name, _, l) ->
    Format.fprintf fmt "th %s: @[<v>%a@]" name
      (Util.print_list_pp ~sep:Format.pp_print_space ~pp:print_atdecl) l
  | TAxiom (_, name, _kind, f) ->
    Format.fprintf fmt "ax %s: @[<hov>%a@]" name (print_formula ~annot) f
  | TRewriting (_, name, l) ->
    Format.fprintf fmt "rwt %s: @[<hov>%a@]" name
      (Util.print_list_pp ~sep:Format.pp_print_space
         ~pp:(print_rwt print_term)) l
  | TGoal (_, sort, name, f) ->
    Format.fprintf fmt "goal %s: @[<hov>%a@]" name print_formula f
  | TPush (_loc,n) ->
    Format.fprintf fmt "push %d" n
  | TPop (_loc,n) ->
    Format.fprintf fmt "pop %d" n

and print_atdecl ?(annot=no_print) fmt a =
  print_annot annot (fun fmt a -> print_tdecl ~annot fmt a.c) fmt a
*)

let fresh_hypothesis_name =
  let cpt = ref 0 in
  fun sort ->
    incr cpt;
    match sort with
    | Thm -> "@H"^(string_of_int !cpt)
    | _ -> "@L"^(string_of_int !cpt)

let is_local_hyp s =
  try String.equal (String.sub s 0 2) "@L" with Invalid_argument _ -> false

let is_global_hyp s =
  try String.equal (String.sub s 0 2) "@H" with Invalid_argument _ -> false
