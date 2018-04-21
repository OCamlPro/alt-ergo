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

open Format
open Parsed

[@@@ocaml.warning "-33"]
open Options

type ('a, 'b) annoted =
    { c : 'a;
      annot : 'b }

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

type 'a tterm =
  { tt_ty : Ty.t; tt_desc : 'a tt_desc }

and 'a tt_desc =
  | TTconst of tconstant
  | TTvar of Symbols.t
  | TTinfix of ('a tterm, 'a) annoted * Symbols.t * ('a tterm, 'a) annoted
  | TTprefix of Symbols.t * ('a tterm, 'a) annoted
  | TTapp of Symbols.t * ('a tterm, 'a) annoted list
  | TTmapsTo of Hstring.t * ('a tterm, 'a) annoted
  | TTinInterval of
      ('a tterm, 'a) annoted * bool * ('a tterm, 'a) annoted *
        ('a tterm, 'a) annoted *  bool
  (* bool = true <-> interval is_open *)

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

and 'a tatom =
  | TAtrue
  | TAfalse
  | TAeq of ('a tterm, 'a) annoted list
  | TAdistinct of ('a tterm, 'a) annoted list
  | TAneq of ('a tterm, 'a) annoted list
  | TAle of ('a tterm, 'a) annoted list
  | TAlt of ('a tterm, 'a) annoted list
  | TApred of ('a tterm, 'a) annoted * bool (* true <-> negated *)
  | TAbuilt of Hstring.t * ('a tterm, 'a) annoted list

and 'a quant_form = {
  (* quantified variables that appear in the formula *)
  qf_bvars : (Symbols.t * Ty.t) list ;
  qf_upvars : (Symbols.t * Ty.t) list ;
  qf_triggers : (('a tterm, 'a) annoted list * bool) list ;
  qf_hyp : ('a tform, 'a) annoted list;
  qf_form : ('a tform, 'a) annoted
}

and 'a tform =
  | TFatom of ('a tatom, 'a) annoted
  | TFop of oplogic * (('a tform, 'a) annoted) list
  | TFforall of 'a quant_form
  | TFexists of 'a quant_form
  | TFlet of (Symbols.t * Ty.t) list *
             (Symbols.t * 'a tlet_kind) list * ('a tform, 'a) annoted
  | TFnamed of Hstring.t * ('a tform, 'a) annoted

and 'a tlet_kind =
  | TletTerm of ('a tterm, 'a) annoted
  | TletForm of ('a tform, 'a) annoted

type 'a rwt_rule = {
  rwt_vars : (Symbols.t * Ty.t) list;
  rwt_left : 'a;
  rwt_right : 'a
}

type goal_sort = Cut | Check | Thm

type theories_extensions =
| Sum
| Arrays
| Records
| Bitv
| LIA
| LRA
| NRA
| NIA
| FPA

type 'a tdecl =
  (* to simplify impl and extension of GUI, a TTtheory is seen a list
     of tdecl, although we only allow axioms in theories
     declarations *)
  | TTheory of
      Loc.t * string * theories_extensions * ('a tdecl, 'a) annoted list
  | TAxiom of Loc.t * string * axiom_kind * ('a tform, 'a) annoted
  | TRewriting of Loc.t * string * (('a tterm, 'a) annoted rwt_rule) list
  | TGoal of Loc.t * goal_sort * string * ('a tform, 'a) annoted
  | TLogic of Loc.t * string list * plogic_type
  | TPredicate_def of
      Loc.t * string *
	(string * ppure_type) list * ('a tform, 'a) annoted
  | TFunction_def of
      Loc.t * string *
	(string * ppure_type) list * ppure_type * ('a tform, 'a) annoted
  | TTypeDecl of Loc.t * string list * string * body_type_decl

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
  | TTnamed (lbl, t) ->
    fprintf fmt "%a" print_term t

  | TTinInterval(e, lb, i, j, ub) ->
    fprintf fmt "%a in %s%a, %a%s"
      print_term e
      (if lb then "]" else "[")
      print_term i
      print_term j
      (if ub then "[" else "]")

  | TTmapsTo(x,e) ->
    fprintf fmt "%s |-> %a" (Hstring.view x) print_term e

  | TTite(cond, t1, t2) ->
    fprintf fmt "(if %a then %a else %a)"
      print_formula cond print_term t1 print_term t2

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
    | TAbuilt(s, l) ->
      fprintf fmt "%s(%a)" (Hstring.view s) print_term_list l
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
      fprintf fmt "%a %s %a" print_formula f1 (string_of_op op) print_formula f2
    | TFforall {qf_bvars = l; qf_triggers = t; qf_form = f} ->
      fprintf fmt "forall %a [%a]. %a"
	print_binders l print_triggers t print_formula f
    | _ -> assert false

and print_form_list fmt = List.iter (fprintf fmt "%a" print_formula)

let th_ext_of_string ext loc =
  match ext with
  | "Sum" -> Sum
  | "Arrays" -> Arrays
  | "Records" -> Records
  | "Bitv" -> Bitv
  | "LIA" -> LIA
  | "LRA" -> LRA

  | "NRA" -> NRA
  | "NIA" -> NIA
  | "FPA" -> FPA
  |  _ ->  Errors.error (Errors.ThExtError ext) loc

let string_of_th_ext ext =
  match ext with
  | Sum -> "Sum"
  | Arrays -> "Arrays"
  | Records -> "Records"
  | Bitv -> "Bitv"
  | LIA -> "LIA"
  | LRA -> "LRA"
  | NRA -> "NRA"
  | NIA -> "NIA"
  | FPA -> "FPA"
