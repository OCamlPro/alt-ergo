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

(** Typed AST

    This module defines a typed AST, used to represent typed terms
    before they are hashconsed. *)

open Parsed

(** {2 Annotations} *)

type ('a, 'b) annoted = {
  c : 'a;
  annot : 'b;
}
(** An annoted structure. Usually used to annotate terms. *)


(** {2 Terms and formulas} *)


type tconstant =
  | Tint of string      (** An integer constant.
                            TODO: make it an arbitrary rpecision integer ? *)
  | Treal of Num.num    (** Real constant. *)
  | Tbitv of string     (** Bitvector constant. *)
  | Ttrue               (** The true boolean (or proposition ?) *)
  | Tfalse              (** The false boolean *)
  | Tvoid               (** TODO: what is this ? *)
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
  | TTmapsTo of Hstring.t * 'a atterm
  (** TODO: what is this ? *)
  | TTinInterval of 'a atterm * bool * 'a atterm * 'a atterm * bool
  (** Represent intervals. (TODO: integer/real/arithmetic intervals ?)
      [TTinInterval (lower, l_strict, t, upper, u_strict)] is a constraint
      stating that term [t] is in the interval [lower, upper],
      and that the lower (resp. upper) bound is strict iff [l_strict]
      (resp. [u_strict]) is true.
      TODO: check that the order of arguments is the correct one ? *)
  | TTget of 'a atterm * 'a atterm
  (** Get operation. TODO: on arrays/bitvectors ? *)
  | TTset of 'a atterm * 'a atterm * 'a atterm
  (** Set operation. TODO: on arrays/bitvectors ? *)
  | TTextract of 'a atterm * 'a atterm * 'a atterm
  (** TODO: what is this ? *)
  | TTconcat of 'a atterm * 'a atterm
  (* Concatenation. TODO: on lists/arrays/bitvectors ? *)
  | TTdot of 'a atterm * Hstring.t
  (** TODO: what is this ? field acess on structs/records ? *)
  | TTrecord of (Hstring.t * 'a atterm) list
  (** Record creation. TODO: check that this is correct. *)
  | TTlet of (Symbols.t * 'a atterm) list * 'a atterm
  (** Let-bindings. Accept a list of mutually recursive le-bindings.
      TODO: check that mutually recursive let-bindings are allowed ? *)
  | TTnamed of Hstring.t * 'a atterm
  (** TODO: what is this ? *)
  | TTite of 'a atform * 'a atterm * 'a atterm
  (** Conditional branching, of the form
      [TTite (condition, then_branch, else_branch)].
      TODO: check order of branches. *)
(** Typed terms descriptors.
    TODO: replace tuples by records (possible inline recors to
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
  (** Disequality. All terms in the set are pairwise distinct.
      TODO: check interpretation ? *)
  | TAneq of 'a atterm list
  (** Equality negation: at least two elements in the list
      are not equal.
      TODO: check interpretation. *)
  | TAle of 'a atterm list
  (** Arithmetic ordering: lesser or equal. Chained on lists of terms.
      TODO: check interpretation ? *)
  | TAlt of 'a atterm list
  (** Strict arithmetic ordering: less than. Chained on lists of terms.
      TODO: check interpretation ? *)
  | TApred of 'a atterm * bool
  (** Term predicate, negated if the boolean is true.
      [TApred (t, negated)] is satisfied iff [t <=> not negated] *)
(** Typed atoms. *)

and 'a quant_form = {
  qf_bvars : (Symbols.t * Ty.t) list;
  (** Quantified variables (with their types) that appear in the formula.
      TODO: reword this to say whether those variables appear int he formula,
            or whether they are the variables quantified by the formula (in the
            inner formula [qf_form]) *)
  qf_upvars : (Symbols.t * Ty.t) list;
  (** TODO: what are thoses ? *)
  qf_triggers : ('a atterm list * bool) list;
  (** Triggers associated wiht the formula.
      TODO: what is the boolean ? *)
  qf_hyp : 'a atform list;
  (** TODO: what is this field ? *)
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
  | TFlet of (Symbols.t * Ty.t) list *
             (Symbols.t * 'a tlet_kind) list *
             'a atform
  (** Let binding.
      TODO: what is in the first list ? *)
  | TFnamed of Hstring.t * 'a atform
  (** TODO: what is this ? *)
(** Typed formulas. *)

and 'a tlet_kind =
  | TletTerm of 'a atterm   (** Term let-binding *)
  | TletForm of 'a atform   (** Formula let-binding *)
(** The different kinds of let-bindings,
    whether they bind terms or formulas. *)


(** {5 Printing} *)

val print_term : Format.formatter -> _ atterm -> unit
(** Print annoted typed terms. Ignore the annotations. *)

val print_formula : Format.formatter -> _ atform -> unit
(**Print annoted typed formulas; Ignores the annotations. *)

val print_binders : Format.formatter -> (Symbols.t * Ty.t) list -> unit
(** Print a list of bound typed variables. *)

val print_triggers : Format.formatter -> ('a atterm list * bool) list -> unit
(** Print a list of triggers. *)




(** {2 Declarations} *)


type 'a rwt_rule = {
  rwt_vars : (Symbols.t * Ty.t) list; (** Variables of the rewrite rule *)
  rwt_left : 'a;          (** Left side of the rewrite rule (aka pattern). *)
  rwt_right : 'a;         (** Right side of the rewrite rule. *)
}
(** Rewrite rules.
    Polymorphic to allow for different representation of terms. *)

type goal_sort =
  | Cut       (** TODO: ? *)
  | Check     (** TODO: ? *)
  | Thm       (** The goal is a theorem to be proved ? *)
(** Goal sort. Used in typed declarations. *)

type theories_extensions =
  | Sum     (** Sum types (aka algebraic datatypes). TODO: check. *)
  | Arrays  (** Functionnal arrays (aka maps). TODO: check.  *)
  | Records (** Records (aka structs) *)
  | Bitv    (** Theory of bitvectors *)
  | LIA     (** Linear Integer Arithmetic *)
  | LRA     (** Linear Real Arithmetic *)
  | NRA     (** Non-linear Real Arithmetic *)
  | NIA     (** Non-linear Integer arithmetic *)
  | FPA     (** Floating Point Arithmetic *)
(** Theories known in alt-ergo, as defined in smtlib. *)

type 'a atdecl = ('a tdecl, 'a) annoted
(** Type alias for annoted typed declarations. *)

and 'a tdecl =
  | TTheory of Loc.t * string * theories_extensions * 'a atdecl list
  (** Theory declarations. The list of declarations in a Theory may
      only contain Axioms. *)
  | TAxiom of Loc.t * string * axiom_kind * 'a atform
  (** New axiom that can be used in proofs. *)
  | TRewriting of Loc.t * string * ('a atterm rwt_rule) list
  (** New rewrite rule that can be used. *)
  | TGoal of Loc.t * goal_sort * string * 'a atform
  (** New goal to prove. *)
  | TLogic of Loc.t * string list * plogic_type
  (** Function (or predicate) type declaration. *)
  | TPredicate_def of
      Loc.t * string * (string * ppure_type) list * 'a atform
  (** Predicate definition.
      [TPredicate_def (loc, name, vars, body)] declares a predicate
      [fun vars => body]. *)
  | TFunction_def of
      Loc.t * string *
      (string * ppure_type) list * ppure_type * 'a atform
  (** Predicate definition.
      [TPredicate_def (loc, name, vars, ret, body)] declares a function
      [fun vars => body], where body has type [ret]. *)
  | TTypeDecl of Loc.t * string list * string * body_type_decl
  (** Type declaration.
      TODO: what are all those strings ?!! *)
(** Typed declarations.
    TODO: wrap this in a record to factorize away
    the location and name of the declaration ? *)


(** {5 Printing} *)

val string_of_th_ext : theories_extensions -> string
(** Returns the string name of the given theory. *)


(** {5 Building functions} *)

val th_ext_of_string : string -> Loc.t -> theories_extensions
(** Parses a string into the typed representation of theories. *)

