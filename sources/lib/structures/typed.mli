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

open Parsed

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
  | TTlet of Symbols.t * ('a tterm, 'a) annoted * ('a tterm, 'a) annoted
  | TTnamed of Hstring.t * ('a tterm, 'a) annoted

type 'a tatom =
  | TAtrue
  | TAfalse
  | TAeq of ('a tterm, 'a) annoted list
  | TAdistinct of ('a tterm, 'a) annoted list
  | TAneq of ('a tterm, 'a) annoted list
  | TAle of ('a tterm, 'a) annoted list
  | TAlt of ('a tterm, 'a) annoted list
  | TApred of ('a tterm, 'a) annoted
  | TAbuilt of Hstring.t * ('a tterm, 'a) annoted list

type 'a oplogic =
    OPand |OPor | OPimp | OPnot | OPiff
  | OPif of ('a tterm, 'a) annoted

type 'a quant_form = {
  (* quantified variables that appear in the formula *)
  qf_bvars : (Symbols.t * Ty.t) list ;
  qf_upvars : (Symbols.t * Ty.t) list ;
  qf_triggers : (('a tterm, 'a) annoted list * bool) list;
  qf_hyp : ('a tform, 'a) annoted list;
  qf_form : ('a tform, 'a) annoted
}

and 'a tform =
  | TFatom of ('a tatom, 'a) annoted
  | TFop of 'a oplogic * (('a tform, 'a) annoted) list
  | TFforall of 'a quant_form
  | TFexists of 'a quant_form
  | TFlet of (Symbols.t * Ty.t) list * Symbols.t *
      ('a tterm, 'a) annoted * ('a tform, 'a) annoted
  | TFnamed of Hstring.t * ('a tform, 'a) annoted


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


val print_term : Format.formatter -> ('a tterm, 'a) annoted -> unit
val print_formula : Format.formatter -> ('a tform, 'a) annoted
  -> unit
val print_binders : Format.formatter -> (Symbols.t * Ty.t) list -> unit
val print_triggers :
  Format.formatter -> (('a tterm, 'a) annoted list * bool) list  -> unit

val th_ext_of_string : string -> Loc.t -> theories_extensions
val string_of_th_ext : theories_extensions -> string
