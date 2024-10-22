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

(** Typed AST

    This module defines a typed AST, used to represent typed terms
    before they are hashconsed. *)


(** {2 Annotations} *)

type ('a, 'b) annoted = {
  c : 'a;
  annot : 'b;
}
(** An annoted structure. Usually used to annotate terms. *)

val new_id : unit -> int
(** Generate a new, fresh integer (useful for annotations). *)

val mk : ?annot:int -> 'a -> ('a, int) annoted
(** Create an annoted value with the given annotation.
    If no annotation is given, a fresh annotation is generated
    using {!new_id}. *)


(** {2 Terms and formulas} *)


type tconstant =
  (* TODO: make Tint hold an arbitrary precision integer ? *)
  | Tint of string        (** An integer constant. *)
  | Treal of Numbers.Q.t  (** Real constant. *)
  | Tbitv of string       (** Bitvector constant. *)
  | Ttrue                 (** The true boolean (or proposition ?) *)
  | Tfalse                (** The false boolean *)
  | Tvoid                 (** The only value of type unit *)
(** Typed constants. *)

type oplogic =
  | OPand       (** conjunction *)
  | OPor        (** disjunction *)
  | OPxor       (** exclusive disjunction *)
  | OPimp       (** implication *)
  | OPnot       (** negation *)
  | OPiff       (** equivalence *)
  | OPif        (** conditional branching *)
(** Logic operators. *)

type pattern =
  | Constr of {
      name : Dolmen.Std.Expr.term_cst ;
      args : (Var.t * Dolmen.Std.Expr.term_cst * Ty.t) list
    }
  | Var of Var.t


type 'a tterm = {
  tt_ty : Ty.t;         (** type of the term *)
  tt_desc : 'a tt_desc; (** term descriptor *)
}
(** Typed terms. Polymorphic in the annotation:
    an ['a tterm] is a term annoted with values of type ['a]. *)

and 'a atterm = ('a tterm, 'a) annoted
(** type alias for annoted typed terms. *)

and 'a tt_desc =
  | TTconst of tconstant
  (** Term constant *)
  | TTvar of Symbols.t
  (** Term variables *)
  | TTinfix of 'a atterm * Symbols.t * 'a atterm
  (** Infix symbol application *)
  | TTprefix of Symbols.t * 'a atterm
  (** Prefix symbol application *)
  | TTapp of Symbols.t * 'a atterm list
  (** Arbitrary symbol application *)
  | TTmapsTo of Var.t * 'a atterm
  (** Used in semantic triggers for floating point arithmetic.
      See sources/preludes/fpa-theory-2017-01-04-16h00.ae *)
  | TTinInterval of 'a atterm * Symbols.bound * Symbols.bound
  (** Represent floating point intervals (used for triggers in Floating
      point arithmetic theory).
      [TTinInterval (lower, l_strict, t, upper, u_strict)] is a constraint
      stating that term [t] is in the interval [lower, upper],
      and that the lower (resp. upper) bound is strict iff [l_strict]
      (resp. [u_strict]) is true. *)
  | TTget of 'a atterm * 'a atterm
  (** Get operation on arrays *)
  | TTset of 'a atterm * 'a atterm * 'a atterm
  (** Set operation on arrays *)
  | TTextract of 'a atterm * int * int
  (** Extract a sub-bitvector *)
  | TTconcat of 'a atterm * 'a atterm
  (* Concatenation of bitvectors *)
  | TTrecord of Ty.t * (Hstring.t * 'a atterm) list
  (** Record creation. *)
  | TTlet of (Symbols.t * 'a atterm) list * 'a atterm
  (** Let-bindings. Accept a list of mutually recursive le-bindings. *)
  (* TODO: check that mutually recursive let-bindings are allowed ? *)
  | TTnamed of Hstring.t * 'a atterm
  (** Attach a label to a term. *)
  | TTite of 'a atform * 'a atterm * 'a atterm
  (** Conditional branching, of the form
      [TTite (condition, then_branch, else_branch)]. *)

  | TTproject of 'a atterm  * Hstring.t
  (** Field (conditional) access on ADTs. *)

  | TTmatch of 'a atterm * (pattern * 'a atterm) list
  (** pattern matching on ADTs *)

  | TTform of 'a atform
  (** formulas inside terms: simple way to add them without making a
      lot of changes *)
(** Typed terms descriptors. *)
(* TODO: replace tuples by records (possible inline records to
         avoid polluting the namespace ?) with explicit field names. *)


and 'a atatom = ('a tatom, 'a) annoted
(** Type alias for annoted typed atoms. *)

and 'a tatom =
  | TAtrue
  (** The [true] atom *)
  | TAfalse
  (** The [false] atom *)
  | TAeq of 'a atterm list
  (** Equality of a set of typed terms. *)
  | TAdistinct of 'a atterm list
  (** Disequality. All terms in the set are pairwise distinct. *)
  | TAneq of 'a atterm list
  (** Equality negation: at least two elements in the list
      are not equal. *)
  | TAle of 'a atterm list
  (** Arithmetic ordering: lesser or equal. Chained on lists of terms. *)
  | TAlt of 'a atterm list
  (** Strict arithmetic ordering: less than. Chained on lists of terms. *)
  | TApred of 'a atterm * bool
  (** Term predicate, negated if the boolean is true.
      [TApred (t, negated)] is satisfied iff [t <=> not negated] *)

  | TTisConstr of 'a atterm  * Hstring.t
  (** Test if the given term's head symbol is identitical to the
      provided ADT consturctor *)


(** Typed atoms. *)

and 'a quant_form = {
  qf_bvars : (Symbols.t * Ty.t) list;
  (** Variables that are quantified by this formula. *)
  qf_triggers : ('a atterm list * bool) list;
  (** Triggers associated wiht the formula.
      For each trigger, the boolean specifies whether the trigger
      was given in the input file (compared to inferred). *)
  qf_hyp : 'a atform list;
  (** Hypotheses of axioms with semantic triggers in FPA theory. Typically,
      these hypotheses reduce to TRUE after instantiation *)
  qf_form : 'a atform;
  (** The quantified formula. *)
}
(** Quantified formulas. *)

and 'a atform = ('a tform, 'a) annoted
(** Type alias for typed annoted formulas. *)

and 'a tform =
  | TFatom of 'a atatom
  (** Atomic formula. *)
  | TFop of oplogic * 'a atform list
  (** Application of logical operators. *)
  | TFforall of 'a quant_form
  (** Universal quantification. *)
  | TFexists of 'a quant_form
  (** Existencial quantification. *)
  | TFlet of (Var.t * 'a tlet_kind) list *
             'a atform
  (** Let binding. *)
  | TFnamed of Hstring.t * 'a atform
  (** Attach a name to a formula. *)

  | TFmatch of 'a atterm * (pattern * 'a atform) list
  (** pattern matching on ADTs *)

(** Typed formulas. *)

and 'a tlet_kind =
  | TletTerm of 'a atterm   (** Term let-binding *)
  | TletForm of 'a atform   (** Formula let-binding *)
(** The different kinds of let-bindings,
    whether they bind terms or formulas. *)


(** {2 Declarations} *)


type 'a rwt_rule = {
  rwt_vars : (Symbols.t * Ty.t) list; (** Variables of the rewrite rule *)
  rwt_left : 'a;          (** Left side of the rewrite rule (aka pattern). *)
  rwt_right : 'a;         (** Right side of the rewrite rule. *)
}
(** Rewrite rules.
    Polymorphic to allow for different representation of terms. *)

type tlogic_type =
  | TPredicate of Ty.t list       (** Predicate type declarations *)
  | TFunction of Ty.t list * Ty.t (** Function type declarations *)
(** Type declarations. Specifies the list of argument types,
    as well as the return type for functions (predicate implicitly
    returns a proposition, so there is no need for an explicit return
    type). *)

type 'a atdecl = ('a tdecl, 'a) annoted
(** Type alias for annoted typed declarations. *)

and 'a tdecl =
  | TTheory of Loc.t * string * Util.theories_extensions * 'a atdecl list
  (** Theory declarations. The list of declarations in a Theory may
      only contain Axioms. *)
  | TAxiom of Loc.t * string * Util.axiom_kind * 'a atform
  (** New axiom that can be used in proofs. *)
  | TRewriting of Loc.t * string * ('a atterm rwt_rule) list
  (** New rewrite rule that can be used. *)
  | TGoal of Loc.t * Ty.goal_sort * string * 'a atform
  (** New goal to prove. *)
  | TLogic of Loc.t * string list * tlogic_type
  (** Function (or predicate) type declaration. *)
  | TPredicate_def of
      Loc.t * string * (string * Ty.t) list * 'a atform
  (** Predicate definition.
      [TPredicate_def (loc, name, vars, body)] defines a predicate
      [fun vars => body]. *)
  | TFunction_def of
      Loc.t * string *
      (string * Ty.t) list * Ty.t * 'a atform
  (** Predicate definition.
      [TPredicate_def (loc, name, vars, ret, body)] defines a function
      [fun vars => body], where body has type [ret]. *)
  | TTypeDecl of Loc.t * Ty.t
  (** New type declaration. [TTypeDecl (loc, vars, t, body)]
      declares a type [t], with parameters [vars], and with
      contents [body]. This new type may either be abstract,
      a record type, or an enumeration. *)
  | TPush of Loc.t * int
  (** [push (loc,n)] pushs n new assertions levels onto the assertion stack *)
  | TPop of Loc.t * int
  (** [pop (loc,n)] pops n assertions levels from the assertion stack *)
  | TReset of Loc.t
  (** Resets all the context. *)
  | TExit of Loc.t
  (** Exits the solver. *)

  | TOptimize of Loc.t * 'a atterm * bool
  (** Optimization declaration.
      [TOptimize (loc, obj, is_max)] declares an objective function [obj]. The
      flag [is_max] determines if we try to maximize of minimize [obj]. *)

(** Typed declarations. *)
(* TODO: wrap this in a record to factorize away
   the location and name of the declaration ? *)


(** {5 Printing} *)

val print_term : Format.formatter -> _ atterm -> unit
(** Print annoted typed terms. Ignore the annotations. *)

val print_formula : Format.formatter -> _ atform -> unit
(**Print annoted typed formulas; Ignores the annotations. *)

val print_binders : Format.formatter -> (Symbols.t * Ty.t) list -> unit
(** Print a list of bound typed variables. *)

val print_triggers : Format.formatter -> ('a atterm list * bool) list -> unit
(** Print a list of triggers. *)

val print_rwt :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a rwt_rule -> unit
(** Print a rewrite rule *)

val print_atdecl : Format.formatter -> _ atdecl -> unit
(** Print an annoted term decl. *)
