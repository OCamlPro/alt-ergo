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

(** {1 Types} *)

type binders = (Ty.t * int) Symbols.Map.t
(** Type of multisets of bound variables in expressions. *)
(*int tag in globally unique *)

type t = private {
  top_sy : Symbols.t;
  (** Top symbol. *)

  args : t list;
  (** List of arguments. *)

  ty : Ty.t;
  (** Type of the expression. *)

  bind : bind_kind;
  (** Kind of binding. *)

  id : int;
  (** Unique identifiant used by the {!module:Hconsing} module. *)

  vars : (Ty.t * int) Symbols.Map.t;
  (** Multiset of the free variables occurred in the expression. *)

  vty : Ty.Svty.t;
  (** Multiset of the free type variables occurred in the expression. *)

  depth : int;
  (** Depth of the expression. *)

  nb_nodes : int;
  (** Number of nodes. *)

  pure : bool;
  (** Flag of pureness. This flag prevents multiple purification. *)

  mutable neg : t option
  (** The negative form of an expression whose the type is
      {!constructor:Ty.Tbool}. Otherwise, this field is equal to [None]. *)
}
(** Type of expression. *)

and decl_kind =
  | Dtheory
  (** Declaration of theory. *)

  | Daxiom
  (** Declaration of axiom. *)

  | Dgoal
  (** Declaration of goal. *)

  | Dpredicate of t
  (** Declaration of predicate. *)

  | Dfunction of t
  (** Declaration of function. *)
(** Kind of declaration. *)

and bind_kind =
  | B_none
  (** No binding. *)

  | B_lemma of quantified
  | B_skolem of quantified
  | B_let of letin
  (** Let binding. *)
(** Type of binding. *)

and quantified = private {
  name : string;
  (** Name of the quantified formula. *)

  main : t;
  (** The formula itself. *)

  toplevel : bool;

  user_trs : trigger list;
  (** Triggers defined by the user. *)

  binders : binders;
  (** Multiset of the bound variables of the formula. *)

  sko_v : t list;
  (* These fields should be (ordered) lists ! important for skolemization *)

  sko_vty : Ty.t list;

  loc : Loc.t;
  (** Location of the "GLOBAL" axiom containing this quantified formula.
      It forms with name a unique id. *)

  kind : decl_kind;
}
(** Type of quantified formulas. More precisely, a quantified formula is
    represented in Skolem normal form, that is a prenex normal form whose
    the existantial quantifiers have been eliminated by introducing Skolem
    functions. *)

and letin = private {
  let_v : Symbols.t;
  (** Symbol of the substitution. *)

  let_e : t;
  (** Expression of substitution. *)

  in_e : t;
  (** Expression in which we apply the substitution. *)

  let_sko : t;
  (** Fresh Skolem function associated with the let-binding. More precisely,
      if the free variables of [let_e] are [x1, ..., xk], the term
      [let_sko] is of the form [f(x1, ..., xk)] where the name [f] is
      guaranteed to be unique. *)

  is_bool : bool;
  (** This flag is [true] if and only if the term [in_e] is of type
      {!const:Ty.Tbool}. *)
}
(** Type of a let expression [let let_v = let_e in in_e]. *)

and semantic_trigger =
  | Interval of t * Symbols.Bound.t * Symbols.Bound.t
  | MapsTo of Var.t * t
  | NotTheoryConst of t
  | IsTheoryConst of t
  | LinearDependency of t * t

and trigger = private {
  content : t list;
  (* this field is filled (with a part of 'content' field) by theories
     when assume_th_elt is called *)
  semantic : semantic_trigger list;
  hyp : t list;
  t_depth : int;
  from_user : bool;
  guard : t option
}

type subst = t Symbols.Map.t * Ty.Subst.t

type lit_view = private
  | Eq of { lhs: t; rhs: t }
  (** Equality of two expression.

      The literal [Eq e_1 e_2] means {m e\_1 = e\_2.} *)

  | Eql of t list
  (** Equality of an arbitrary number of expressions.

      The literal [Eql [e_1; e_2; ...; e_k]] means
      {m e\_1 = e\_2 = \cdots = e\_k.} *)

  | Distinct of t list
  (** Disequality of an arbitrary number of expressions.

      The literal [Distinct [e_1; e_2; ...; e_k]] means
      {m e\_1 \not= e\_2 \not= \cdots \not= e\_k.}*)

  | Builtin of bool * Symbols.builtin * t list
  | Pred of t * bool
  (** Predicate.

      The literal [Pred (t, true)] denotes the predicate [t] and
      [Pred (t, false)] denotes its negative form. *)
(** View of literal. *)

type form_view = private
  | Unit of t * t
  (** Unit clauses. *)

  | Clause of t * t * bool
  (** [Clause (f1, f2, is_imply)] is the clause {m f1 |lor f2}
      when [is_imply] is [false] and the implication {m f1 \Longrightarrow f2}
      otherwise. *)

  | Iff of t * t
  (** [Iff (f1, f2)] is the equivalence {m f1 \Longleftrightarrow f2}. *)

  | Xor of t * t
  (** [Xor (f1, f2)] is the exclusive or {m f1 \oplus f2}. *)

  | Literal of t
  (** A literal formula. *)

  | Lemma of quantified
  (** A lemma. *)

  | Skolem of quantified
  (** Lazy skolemization. *)

  | Let of letin
  (** A let binding of an expr. *)
(** View of form. *)

(** {1 Data structures} *)

module Set : Set.S with type elt = t
(** Module of sets of expressions using {!val:compare} as
    comparison function. *)

module Map : Map.S with type key = t
(** Module of maps of expression keys using {!val:compare} as
    comparion function. *)

(** {1 Views} *)

val lit_view : t -> lit_view
val form_view : t -> form_view

(** {1 Smart constructors} *)

val mk_binders : Set.t -> binders

val mk_ite : cond:t -> then_:t -> else_:t -> t
(** [mk_ite cond then_ else_] produces the expression
    [if cond then then_ else else_].
    If the expressions [then_] and [else_] are of type {!constructor:Ty.Tbool},
    the function produces the formula [mk_if cond then_ else_] instead. *)

val mk_let: var:Symbols.t -> let_e:t -> in_e:t -> t
(** [mk_let sy e1 e2] constructs the expression [let sy = e1 in e2].
    Obvious substitutions are inlined during the construction. *)

val mk_match: t -> (Typed.pattern * t) list -> t

(** {2 For terms} *)

val mk_term: sy:Symbols.t -> args:t list -> ty:Ty.t -> t
(** [mk_term sy args ty] creates a term whose the top symbol is
    [sy], the arguments are [args] and its type witness is [ty]. *)

val pred: t -> t
(** [pred t] produces the expression [t-1]. *)

(** {3 Literal expressions} *)

val void : t
(** The unit expression. *)

val int : string -> t
(** [int str] produces the integer literal corresponding to
    the string representaiton [str]. *)

val real : string -> t
(** [real str] produces the real literal corresponding to
    the string representation [str]. *)

val bitv : string -> Ty.t -> t
(** [bitv str] produces the bitvector literal corresponding to
    the string representaiton [str]. *)

val fresh_name : ty:Ty.t -> t
(** [fresh_name ~ty] produces a fresh variable of type [ty]. *)

(** {2 For literals} *)

val mk_eq : use_equiv:bool -> t -> t -> t
(** [mk_eq ~use_equiv tm1 tm2] produces an equivalent formula to
    the formula [tm1 = tm2]. If [use_equiv] is [true] and [t1] and [t1] are
    of type {!constructor:Ty.Tbool} then the function produces a formula
    equivalent to {m tm1 \iff tm2}. *)

val mk_nary_eq : t list -> t
(** [mk_nary_eq lst] produces an equivalent formula to
    the formula [tm1 = tm2 = ... = tmk] where [lst = [tm1; tm2; ...; tmk]]. *)

val mk_distinct : use_equiv:bool -> t list -> t
val mk_builtin : is_pos:bool -> builtin:Symbols.builtin -> args:t list -> t

(** {2 For formulas} *)

(* TODO: Rename the function true_. *)
val vrai : t
(** The true formula. *)

(* TODO: Rename the function false_. *)
val faux : t
(** The false formula. *)

val mk_or : ?is_imply:bool -> t -> t -> t
(** [mk_or f1 f2] produces a formula equivalent to the {e disjunction}
    {m f1 \lor f2} of the formula [f1] and [f2]. *)

val mk_and : ?is_imply:bool -> t -> t -> t
(** [mk_and f1 f2] produces a formula equivalent to the {e conjunction}
    {m f1 \land f2} of the formula [f1] and [f2]. *)

val mk_imp : t -> t -> t
(** [mk_imp f1 f2] produces a formula equivalent to the {e implication}
    {m f1 \implies f2}. *)

val mk_iff : t -> t -> t
(** [mk_iff f1 f2] produces a formula equivalent to the {e equivalence}
    {m f1 \iff f2}. *)

val mk_if : t -> t -> t -> t
(** [mk_if f1 f2] produces a formula equivalent to {m f1 \vee f2}. *)

val mk_xor : t -> t -> t
(** [mk_xor f1 f2] produces a formula equivalent to the {e exclusive
    disjunction} of the formula [f1] and [f2], that is {m f1 \oplus f2}. *)

(** {1 Iterators on subterms} *)

val sub_terms: Set.t -> t -> Set.t
(** [sub_term acc exp] returns the accumulator [acc] augmented
    with the term [exp] and all its sub-terms.
    Return the [acc] if [exp] is not a term. Does not go
    through literals (except positive uninterpreted predicates
    application) and formulas *)

val max_pure_subterms: t -> Set.t
(** [max_pure_subterms exp] returns the set of maximal pure terms of
    the expression [exp]. *)

val max_terms_of_lit: t -> Set.t
(** [max_terms_of_lit lit] returns the maximal terms of the
    literal [lit]. Assertion failure if [lit] is not a literal. *)

val max_ground_terms_of_lit: t -> Set.t
(** [max_ground_terms_of_lit lit] returns the maximal ground terms of the
    given literal [lit]. Raise an assertion if [lit] is not a literal. *)

val atoms_rec_of_form: only_ground:bool -> t -> Set.t -> Set.t
(** [atoms_rec_of_form ~only_ground f acc] traverses a formula recursively
    and collects its atoms. Only ground atoms are kept
    if ~only_ground is [true]. *)

val max_ground_terms_rec_of_form: t -> Set.t
(** [max_ground_terms_rec_of_form f] traverses a formula recursively
    and collects its maximal ground terms. *)

(** {1 Comparison and test functions} *)

val compare: t -> t -> int
(** [compare e1 e2] compares two expressions [e1] and [e2]. More
    precisely, if {m <} denotes the total order defined by [compare], we have
    {math e1 < e2 \iff (depth e1, hash e1)
    \prec (depth e2, hash e2)}
    where {m \prec} is the lexicographic order. *)

val equal : t -> t -> bool
(** [equal e1 e2] is [true] if and only if the expressions
    [e1] and [e2] are physically equal. *)

val hash : t -> int
(** [hash e] returns the hash of the expression [e] used by the hconsing
    module. *)

val compare_subst : subst -> subst -> int
(** [compare_subst sub1 sub2] compares two substitutions [sub1] and [sub2]
    using the lexicographic order on . *)

val equal_subst : subst -> subst -> bool
val compare_quant : quantified -> quantified -> int
val compare_let : letin -> letin -> int

val is_fresh : t -> bool
val is_fresh_skolem : t -> bool

val is_int : t -> bool
(** [is_int e] is true if and only if the expression [e]
    is of type [Ty.Tint]. *)

val is_real : t -> bool
(** [is_real e] is true if and only if the expression [e]
    is of type [Ty.Treal]. *)

val is_positive : t -> bool

val is_pure : t -> bool

val is_ground : t -> bool
(** [is_ground e] is [true] if and only if the expression [e] is ground,
    that is if [e] does not contain free variable or free type variable. *)

(* TODO: Rename this function to is_const_term *)
(** [const_term tm] returns true if and only if the expression
    [tm] is a term without arguments. *)
val const_term : t -> bool

(** {1 Labeling and models} *)

val add_label : Hstring.t -> t -> unit
val label : t -> Hstring.t
val name_of_lemma : t -> string
val name_of_lemma_opt : t option -> string
val print_tagged_classes : Format.formatter -> Set.t list -> unit

(** {1 Substitutions} *)

val apply_subst : subst -> t -> t
val apply_subst_trigger : subst -> trigger -> trigger

(** skolemization and other smart constructors for formulas **)
val mk_trigger :
  name: string ->
  content: t list ->
  guard: t option ->
  hyp: t list ->
  in_theory: bool ->
  from_user: bool ->
  trigger

val make_triggers :
  t ->
  binders ->
  decl_kind ->
  Util.matching_env ->
  trigger list



val resolution_triggers :
  is_back:bool ->
  quantified ->
  trigger list

val partition_patterns :
  trigger ->
  f:(t -> [`Syn of t | `Sem of semantic_trigger]) ->
  trigger


val mk_forall:
  name:string ->
  loc:Loc.t ->
  binders -> (* quantified variables *)
  triggers:trigger list -> (* triggers *)
  toplevel:bool -> (* for future triggers computation in presence of vty *)
  decl_kind:decl_kind ->
  t -> (* quantified formula *)
  t

val mk_exists:
  name:string ->
  loc:Loc.t ->
  binders -> (* quantified variables *)
  triggers:trigger list -> (* triggers *)
  toplevel:bool -> (* for future triggers computation in presence of
                      vty, and to construct a toplevel forall that
                      cover vtys *)
  decl_kind:decl_kind ->
  t -> (* quantified formula *)
  t

val skolemize : quantified -> t

val elim_let : recursive:bool -> letin -> t

val elim_iff : t -> t -> with_conj:bool -> t
(** [elim_iff f1 f2 with_conj] construct an equivalent formula
    to {m f1 \iff f2} using a combinaison of negations, disjunctions
    and conjuctions instead of the built-in symbol {!constructor:Sy.F_Iff}.
    If [with_conj] is [false], the construction doesn't use conjuction. *)

val concat_chainable: Symbols.t -> Ty.t -> t -> t list -> t list

type gformula = {
  ff : t;
  nb_reductions : int;
  trigger_depth : int;
  age : int;
  lem : t option;
  origin_name : string;
  from_terms : t list;
  mf : bool;
  gf : bool;
  gdist : int; (* dist to goal *)
  hdist : int; (* dist to hypotheses *)
  theory_elim : bool;
}

type th_elt = {
  th_name : string;
  ax_name : string;
  ax_form : t;
  extends : Util.theories_extensions;
  axiom_kind : Util.axiom_kind;
}

val print_th_elt : Format.formatter -> th_elt -> unit

(** {1 Misc} *)

val type_info : t -> Ty.t
(** [type_info t] return the type of the expression [t]. *)

val symbol_info : t -> Symbols.t

val print : Format.formatter -> t -> unit
(** [print fmt exp] pretty print the expression [exp] with
    the printer [fmt]. *)

val print_triggers : Format.formatter -> trigger list -> unit
(** [print_triggers fmt lst] pretty print the list of triggers [lst] with
    the printer [fmt]. *)

(* TODO: Move these functions. *)
val print_list : Format.formatter -> t list -> unit
val print_list_sep : string -> Format.formatter -> t list -> unit

val free_vars : t -> (Ty.t * int) Symbols.Map.t
(** [free_vars e] return the multiset of free variables in the term [e]. *)

val free_type_vars : t -> Ty.Svty.t
(** [free_type_vars e] return the set of the free type variables
    occuring in the expression [e]. *)

val size : t -> int
(** [size exp] return the size of the expression [exp]. *)

val depth : t -> int
(** [depth exp] return the depth of the expression [exp]. *)

val neg : t -> t
(** [neg exp] return the negative form of an expression [exp] of type
    {!constructor:Ty.Tbool}.
    Raise an assertion if [exp] is not of type {!constructor:Ty.Tbool}. *)

val save_cache : unit -> unit
(** Saves the modules cache. *)

val reinit_cache : unit -> unit
(** Reinitializes the module's cache. *)
