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
  | Tint of string      (** An integer constant. *)
  | Treal of Num.num    (** Real constant. *)
  | Tbitv of string     (** Bitvector constant. *)
  | Ttrue               (** The true boolean (or proposition ?) *)
  | Tfalse              (** The false boolean *)
  | Tvoid               (** The only value of type unit *)
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
  | Constr of { name : Hstring.t ; args : (Var.t * Hstring.t * Ty.t) list}
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
      See sources/preludes/fpa-theory-2017-01-04-16h00.why *)
  | TTinInterval of 'a atterm * Symbols.bound * Symbols.bound
  (** Represent floating point intervals (used for triggers in Floating
      point arithmetic theory).
      [TTinInterval (t, lower, upper)] is a constraint
      stating that term [t] is between its lower and upper bound. *)
  | TTget of 'a atterm * 'a atterm
  (** Get operation on arrays *)
  | TTset of 'a atterm * 'a atterm * 'a atterm
  (** Set operation on arrays *)
  | TTextract of 'a atterm * 'a atterm * 'a atterm
  (** Extract a sub-bitvector *)
  | TTconcat of 'a atterm * 'a atterm
  (* Concatenation of bitvectors *)
  | TTdot of 'a atterm * Hstring.t
  (** Field access on structs/records *)
  | TTrecord of (Hstring.t * 'a atterm) list
  (** Record creation. *)
  | TTlet of (Symbols.t * 'a atterm) list * 'a atterm
  (** Let-bindings. Accept a list of sequential let-bindings. *)
  | TTnamed of Hstring.t * 'a atterm
  (** Attach a label to a term. *)
  | TTite of 'a atform * 'a atterm * 'a atterm
  (** Conditional branching, of the form
      [TTite (condition, then_branch, else_branch)]. *)

  | TTproject of bool * 'a atterm  * Hstring.t
  (** Field (conditional) access on ADTs. The boolean is true when the
      projection is 'guarded' and cannot be simplified (because
      functions are total) *)

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

  | TTisConstr of ('a tterm, 'a) annoted  * Hstring.t
  (** Test if the given term's head symbol is identitical to the
      provided ADT consturctor *)


(** Typed atoms. *)

and 'a quant_form = {
  qf_bvars : (Symbols.t * Ty.t) list;
  (** Variables that are quantified by this formula. *)
  qf_upvars : (Symbols.t * Ty.t) list;
  (** Free variables that occur in the formula. *)
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
  | TFlet of (Symbols.t * Ty.t) list *
             (Symbols.t * 'a tlet_kind) list *
             'a atform
  (** Let binding. [TFlet (fv, bv, body)] represents the binding
      of the variables in [bv] (to the corresponding term or formula),
      in the formula [body]. The list [fv] contains the list of free term
      variables (together with their type) that occurs in the formula. *)
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


type goal_sort =
  | Cut
  (** Introduce a cut in a goal. Once the cut proved,
      it's added as a hypothesis. *)
  | Check
  (** Check if some intermediate assertion is prouvable *)
  | Thm
  (** The goal to be proved *)
(** Goal sort. Used in typed declarations. *)

val fresh_hypothesis_name : goal_sort -> string
(** create a fresh hypothesis name given a goal sort. *)

val is_local_hyp : string -> bool
(** Assuming a name generated by {!fresh_hypothesis_name},
    answers whether the name design a local hypothesis ? *)

val is_global_hyp : string -> bool
(** Assuming a name generated by {!fresh_hypothesis_name},
    does the name design a global hypothesis ? *)


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
  | TGoal of Loc.t * goal_sort * string * 'a atform
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

val print_goal_sort : Format.formatter -> goal_sort -> unit
(** Print a goal sort *)

val print_rwt :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a rwt_rule -> unit
(** Print a rewrite rule *)


(** {2 Expressions} *)

module Safe : sig

  type t =
    | Term of int atterm  (** Terms *)
    | Atom of int atatom  (** Atoms *)
    | Form of int atform * Ty.tvar list
    (** Formulas additionally carry their set of explicitly quantified
        type variables, in order to disallow deep type quantification. *)
  (** An expression is either a term, an atom, or a formula. *)

  val ty : t -> Ty.t
  (** Return the type of the given expression. *)

  module Var : sig

    type t
    (** Typed variables *)

    val hash : t -> int
    (** hash function *)

    val equal : t -> t -> bool
    (** equality funciton *)

    val compare : t -> t -> int
    (** comparison function *)

    val mk : string -> Ty.t -> t
    (** Create a typed variable from a name and type. *)

    val make : Symbols.t -> Ty.t -> t
    (** Create a typed variable from a symbol and type. *)

    val ty : t -> Ty.t
    (** Return the type of a typed variable. *)

  end

  module Const : sig

    type t
    (** Typed function symbols (aka constants) *)

    val hash : t -> int
    (** hash function *)

    val equal : t -> t -> bool
    (** equality funciton *)

    val compare : t -> t -> int
    (** comparison function *)

    val arity : t -> int * int
    (** Return the expected number of arguments of the constants.
        The pair contains first the number of expected type
        arguments (for polymorphic functions), and then the number
        of reguler (or term) arguments. *)

    val mk : Symbols.t -> Ty.tvar list -> Ty.t list -> Ty.t -> t
    (** Create a typed funciton symbol. Takes as arguments the
        symbol of the function, the type variables that occur in its
        type, the list of argument's expected types, and the function
        return type. *)

  end

  (** {5 Typing exceptions} *)

  exception Term_expected
  (** Raised by function that expect an expression to be
      a term, but the expression was an atom or formula. *)

  exception Formula_expected
  (** Raised by function that expect an expression to be
      a formula, but the expression was a term. *)

  exception Formula_in_term_let
  (** Current typed term structure restricts let-bindings in terms
      to only bind variables to terms and not formulas. *)

  exception Deep_type_quantification
  (** Alt-ergo restricts type variables to be quantified at the
      top of formulas. This exception is raised when trying to
      build a formula that contain a formula with explicitly
      quantified type variables. *)

  exception Wrong_type of t * Ty.t
  (** [Wrong_type (t, ety)] is raised by function that checks
      and compute the type of expressions, when an expression
      was expected to have type [ety], but doe snot have that
      type (as returned by the {! ty} function). *)

  exception Wrong_arity of Const.t * int * int
  (** [Wrong_arity (c, n, m)] is raised when a constant [c]
      is applied to [n] number of type arguments and [m] term
      arguments, but these number do not match the arity of [c],
      as defined by {! Const.arity}. *)

  (** {3 Expression building} *)

  val apply : Const.t -> Ty.t list -> t list -> t
  (** Apply the given typed funciton symbol to the list of
      types and terms given. Automatically checks that the arguments
      have the correct type, and computes the type of the resulting
      expression.
      @raise Wrong_arity
      @raise Wrong_type
      @raise Term_expected
  *)

  val _true : t
  (** The [true] expression *)

  val _false : t
  (** The [false] expression *)

  val eq : t -> t -> t
  (** Create an equality between two expressions.
      @raise Wrong_type
      @raise Term_expected
  *)

  val distinct : t list -> t
  (** Create a distinct expression.
      @raise Wrong_type
      @raise Term_expected
  *)

  val neg : t -> t
  (** Propositional negation
      @raise Formula_expected
      @raise Deep_type_quantification
  *)

  val imply : t -> t -> t
  (** Propositional implication
      @raise Formula_expted
      @raise Deep_type_quantification
  *)

  val equiv : t -> t -> t
  (** Propositional equivalence
      @raise Formula_expected
      @raise Deep_type_quantification
  *)

  val xor : t -> t -> t
  (** Propositional exclusive disjunction
      @raise Formula_expected
      @raise Deep_type_quantification
  *)

  val _and : t list -> t
  (** Propositional conjunction
      @raise Formula_expected
      @raise Deep_type_quantification
  *)

  val _or : t list -> t
  (** Propositional disjunction
      @raise Formula_expected
      @raise Deep_type_quantification
  *)

  val fv : t -> Ty.tvar list * Var.t list
  (** Return the list of free variables that occur in a given term *)

  val all :
    (Ty.tvar list * Var.t list) ->
    (Ty.tvar list * Var.t list) ->
    t -> t
  (** Universal quantification. Accepts as first pair the lists
      of free variables that occur in the resulting formula, then
      the lists of variables quantified in the formula, and then the body
      of the quantified formula.
      @raise Formula_expected
      @raise Deep_type_quantification
  *)

  val ex :
    (Ty.tvar list * Var.t list) ->
    (Ty.tvar list * Var.t list) ->
    t -> t
  (** Existencial quantification. Accepts as first pair the lists
      of free variables that occur in the resulting formula, then
      the lists of variables quantified in the formula, and then the body
      of the quantified formula.
      @raise Formula_expected
      @raise Deep_type_quantification
  *)

  val letin : (Var.t * t) list -> t -> t
  (** Let-binding.
      @raise Deep_type_quantification
  *)

end
