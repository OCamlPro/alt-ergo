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


(** Rewrite rules *)

type 'a rwt_rule = {
  rwt_vars : (Symbols.t * Ty.t) list;
  rwt_left : 'a;
  rwt_right : 'a
}

let print_rwt pp fmt r =
  Format.fprintf fmt "@<hv>%a@ --> %a@]" pp r.rwt_left pp r.rwt_right


(** Goal sort *)

type goal_sort = Cut | Check | Thm | Sat

let print_goal_sort fmt = function
  | Cut -> Format.fprintf fmt "cut"
  | Check -> Format.fprintf fmt "check"
  | Thm -> Format.fprintf fmt "thm"
  | Sat -> Format.fprintf fmt "sat"


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
  | TAdistinct l ->
    fprintf fmt "distinct(%a)" print_term_list l
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
  | TFforall { qf_bvars = l; qf_triggers = t; qf_form = f; _ } ->
    fprintf fmt "forall %a [%a]. %a"
      print_binders l print_triggers t print_formula f

  | TFlet (_, binders, f) ->
    List.iter
      (fun (sy, let_e) ->
         fprintf fmt " let %a = " Symbols.print sy;
         match let_e with
         | TletTerm t -> fprintf fmt "%a in@." print_term t
         | TletForm f -> fprintf fmt "%a in@." print_formula f
      )binders;
    fprintf fmt "%a" print_formula f
  | _ -> fprintf fmt "(formula pprint not implemented)"

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
  | TPush (_loc,n) ->
    Format.fprintf fmt "push %d" n
  | TPop (_loc,n) ->
    Format.fprintf fmt "pop %d" n

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
  try String.equal (String.sub s 0 2) "@L" with Invalid_argument _ -> false

let is_global_hyp s =
  try String.equal (String.sub s 0 2) "@H" with Invalid_argument _ -> false
