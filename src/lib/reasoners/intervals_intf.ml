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

(** Interface for union-of-interval modules. *)

type 'a interval = { lb : 'a ; ub : 'a }
(** The type of {b closed} intervals over type ['a].

    An interval [{ lb ; ub }] represents the closed interval {m [lb, ub]}, i.e.
    a value [v] is in the interval iff [lb <= v <= ub]. *)

type 'a bound =
  | Open of 'a (** An open (strict) finite bound. *)
  | Closed of 'a (** A closed (large) finite bound. *)
  | Unbounded (** An infinite bound. *)
(** The type ['a bound] is used to create and inspect intervals; see
    {!OrderedType.view} and {!Interval.of_bounds}. *)

(** Type signature for explanations. This is mostly intended for Alt-Ergo's
    built-in {!Explanation} module, but it can be convenient to use a
    different module for debugging. *)
module type Explanations = sig
  type t
  (** The type of explanations.

      Explanation encode predicates that may hold (be [true]) or not (be
      [false]) in a model. *)

  val pp : t Fmt.t
  (** Pretty-printer for explanations. *)

  val is_empty : t -> bool
  (** An explanation is empty if it is [true] in all models. *)

  val empty : t
  (** The [empty] explanation. Must satisfy [is_empty empty = true]. *)

  val union : t -> t -> t
  (** The union [union ex ex'] of two explanations [ex] and [ex'] is [true] in
      any model where both [ex] and [ex'] are [true].

      Note that [union ex empty = union empty ex = ex]. *)

  val compare : t -> t -> int
  (** Arbitrary comparison function on explanations. In case multiple
      explanations for a given fact are possible, the smaller explanation
      according to this comparison function is preferred.

      It is recommended, but not required, that {!empty} be the lowest
      explanation for [compare]. *)
end

module type OrderedType = sig
  (** An ordered type of finite values, extended with positive and negative
      infinites as well as successor and predecessor functions to represent
      strict lower and upper bounds.

      Negative and positive infinites are used to represent half-planes as
      intervals; we require that all values are larger than the negative
      infinite and smaller than the positive infinite.

      Values of the form {m x + \epsilon} and {m x - \epsilon} are used to
      transform open bounds in the {!type-finite} type into closed bounds on the
      extended type {!t}, with the equivalence:

      {math
        y <= x - \epsilon \Leftrightarrow y < x
      }

      and

      {math
        x + \epsilon <= y \Leftrightarrow y < x
      }

      This signature does not expose {m x + \epsilon} and {m x - \epsilon}
      values directly; instead, we use {m \mathrm{succ}} and {m \mathrm{pred}}
      functions which can be thought of as addition and subtraction of
      {m \epsilon}, respectively. *)

  type finite
  (** The type of finite values. *)

  val pp_finite : finite Fmt.t
  (** Pretty-printer for finite values. *)

  type t
  (** The type of extended values used to represent interval bounds. *)

  val pp : t Fmt.t
  (** Pretty-printer for extended values. *)

  val equal : t -> t -> bool
  (** Equality on extended values. Must be compatible with [compare]. *)

  val compare : t -> t -> int
  (** The comparison function on extended values is an extension of the regular
      order on finite values. *)

  val view : t -> finite bound
  (** [view t] converts the internal representation to a [bound] for
      examination. *)

  val minfty : t
  (** [minfty] is an extended value {m -\infty} such that for any extended value
      {m x}, {m -\infty \le x}. *)

  val finite : finite -> t
  (** Finite values are included in [t]. We will identify a finite value in
      [finite] and its representation in [t]. *)

  val pinfty : t
  (** [pinfty] is an extended value {m +\infty} such that for any extended value
      {m x}, {m x \le +\infty}. *)

  val value_opt : t -> finite option
  (** [value_opt] is the partial inverse of [finite]. *)

  val succ : t -> t
  (** Each element of the ordered type [t] has a successor. The successor
      of an element is always greater than the element itself:

      {math
        \forall x, x \le \mathrm{succ}(x)
      }

      We say that {m x} is a {e finite upper bound} if it is {e strictly}
      smaller than its successor, i.e. if {m x < \mathrm{succ}(x)}, and we
      require that all {b finite} values are finite upper bounds (however there
      may be finite upper bounds that are not finite values).

      [succ] must be the inverse of [pred] below. *)

  val pred : t -> t
  (** Each element of the ordered type [t] has a predecessor. The predecessor
      of an element is always smaller than the element itself:

      {math
        \forall x, \mathrm{pred}(x) \le x
      }

      We say that {m x} is a {e finite lower bound} if it is {e strictly}
      greater than its predecessor, i.e. if {m \mathrm{pred}(x) < x}, and we
      require that all {b finite} values are finite lower bounds (however there
      may be finite lower bounds that are not finite values).

      [pred] must be the inverse of [succ] above. *)
end

(** Intervals over an {!OrderedType}. *)
module type Interval = sig
  type value
  (** The type of values in the interval. *)

  type bnd
  (** The type of the interval bounds. *)

  type t = bnd interval
  (** The type of {b closed} intervals with bounds of type [bound].

      Note that the {b values} of the interval may have a different type; for
      instance, {m -\infty} and {m +\infty} are valid bounds for real intervals,
      but are not themselves reals.

      We say that an extended value {m x} is a {b valid lower bound} if it
      satisfies:

      {math
        \forall y, y < x \Rightarrow \mathrm{pred}(x) < x
      }

      Similarly, we say that an extended value {m x} is a {b valid upper bound}
      if it satisfies:

      {math
        \forall y, x < y \Rightarrow x < \mathrm{succ}(x)
      }

      Remark that valid lower bounds are either {m -\infty} or finite lower
      bounds, and valid upper bounds are either {m +\infty} or finite upper
      bounds.

      We require that an interval [{ lb ; ub }] be such that [lb] is a valid
      lower bound, [ub] is a valid upper bound, and [lb <= ub]. *)

  val pp : t Fmt.t
  (** Pretty-printer for intervals. *)

  val equal : t -> t -> bool
  (** Equality test for intervals. *)

  val of_bounds : value bound -> value bound -> t
  (** Build an interval from a pair of lower and upper bounds.

      @raises Invalid_argument if the upper bound is smaller than the lower
      bound. *)

  val view : t -> value bound interval
  (** Returns a view of the interval using the [bound] type for convenient
      examination. *)

  val singleton : value -> t
  (** The interval [singleton v] contains the singleton {m \{ v \}}.

      This is an equivalent shortcut for [of_bounds (Closed v) (Closed v)]. *)

  val full : t
  (** The full interval {m [-\infty, +\infty]} contains all values.

      This is an equivalent shortcut for [of_bounds Unbounded Unbounded]. *)

  val value_opt : t -> value option
  (** If the interval is a singleton containing a single value, returns that
      value; otherwise, returns [None]. *)
end

type ('a, 'b) kind =
  | NonEmpty of 'a (** A {b non-empty} value of type ['a]. *)
  | Empty of 'b (** An empty value with additional justification. *)
(** The [kind] type is an equivalent to the [result] type from the standard
    library with more appropriate constructor names.

    It is used to distinguish between unions of intervals that are empty in the
    current context (with an explanation abstracting a set of model where the
    union is also empty) and unions of intervals that have at least one value in
    the current context. *)

module type Union = sig
  (** Signature for union-of-intervals implementations {b with explanations}. *)

  (** Given an explanation {m e} (see {!Intervals_intf.Explanations}), we say
      that an interval {m I} is forbidden for a variable {m x} by {m e} if
      {m M(x)} is never in {m I} when {m M} is a model such that {m M(e)} is
      [true], i.e. if the following implication holds:

      {math \forall M, M(e) \Rightarrow M(x) \not\in I}

      Given a current context {m C} (a set of explanations) and an implicit
      variable {m x}, we say that an interval {m I} is {e forbidden} if it is
      forbidden by an union of explanations in {m C}, and that it is {e allowed}
      otherwise.

      It is always sound to weaken a forbidden interval interval: if {m M(e_1)
      \Rightarrow M(e_2)} and {m I} is forbidden by [e_2], it is also forbidden
      by [e_1].

      (Note that in terms of explanations, this means adding more terms in the
      explanation, since [Explanation.empty] is true in all contexts and since
      [Explanation.union e1 e2] evaluates to {m M(e_1) \wedge M(e_2)}.)

      The [union] type below internally keeps track of both allowed and
      forbidden intervals, where each forbidden interval is annotated by a
      specific explanation (true in the current context) that forbids it, but
      the functions in this module provide abstractions to deal with the unions
      without having to worry about explanations (and forbidden intervals)
      directly.

      In order to avoid having to worry about variables while reasoning about
      intervals, we define a contextual evaluation function for unions (and set
      of intervals); the evaluation of an allowed interval {m I} is always {m I}
      in all contexts, and the evaluation of a forbidden interval {m I} is {m I}
      in contexts where the associated explanation {b does not hold}, and the
      empty set otherwise (in particular, it is the empty set in the current
      context).

      Note that the evaluation of a forbidden interval is a subset of the
      interval in any context. *)

  type explanation
  (** The type of explanations. *)

  type value
  (** The type of values. *)

  type bnd
  (** The type of bounds. *)

  type 'a union

  type t = bnd union
  (** The type of unions. *)

  module Interval : Interval
    with type value = value
     and type bnd = bnd
  (** Intervals over the [value] type. *)

  val pp : t Fmt.t
  (** Pretty-printer for unions. *)

  (** {1 Creation}

      The following functions are used to create unions. *)

  val of_interval :
    ?ex:explanation -> bnd interval -> t
  (** Build an union from an interval.

      [of_interval ?ex:None i] evaluates to [i] in all contexts.

      [of_interval ~ex i] evaluates to [i] in contexts where [ex] holds
      (including the current context) and to the full set otherwise. *)

  val of_bounds :
    ?ex:explanation -> value bound -> value bound -> t
  (** [of_bounds ?ex lb ub] is a shortcut for
      [of_interval ?ex @@ Interval.of_bounds lb ub] *)

  val of_complement :
    ?ex:explanation -> bnd interval -> (t, explanation) kind
  (** Build an union from the complement of an interval.

      The explanation, if provided, justifies that the value is {b not} in the
      interval; the resulting union evaluates to the complement of the interval
      in any model where the explanation holds, and to the full set otherwise.

      If the provided interval covers the full domain, the resulting union is
      empty and an [Empty] kind is returned; otherwise, the resulting union is
      [NonEmpty]. *)

  (** {1 Inspection}

      The following functions are used to inspect the global bounds of an
      union of intervals. *)

  val lower_bound : t -> value bound * explanation
  (** [lower_bound u] returns a pair [lb, ex] of a global lower bound and an
      explanation that justifies that this lower bound is valid. *)

  val upper_bound : t -> value bound * explanation
  (** [upper_bound u] returns a pair [lb, ex] of a global upper bound and an
      explanation that justifies that this upper bound is valid. *)

  val value_opt : t -> (value * explanation) option
  (** If [u] is a singleton {b in the current context}, [value_opt u] returns a
      pair [(v, ex)] where [v] is the value of [u] in the current context and
      [ex] justifies [v] being both a lower and upper bound.

      This is more efficient than checking if the values returned by
      [lower_bound] and [upper_bound] are equal. *)

  (** {1 Iteration}

      The following functions are used to iterate over the maximal disjoint
      intervals composing the union {b in the current context}.  *)

  val to_seq : t -> bnd interval Seq.t
  (** Convert an union of interval to a sequence of maximal disjoint and
      non-adjacent intervals.

      {b Warning}: The sequence of intervals is only valid in the current
      context. *)

  val iter : (bnd interval -> unit) -> t -> unit
  (** [iter f u] calls [f] on each of the maximal disjoint and non-adjacent
      intervals that make up the union [u] {b in the current context}. *)

  val fold : ('a -> bnd interval -> 'a) -> 'a -> t -> 'a
  (** [fold f acc u] folds [f] over each of the maximal disjoint and
      non-adjacent intervals that make up the union [u] {b in the current
      context}. *)

  (** {1 Comparison}

      The following functions are used to compare intervals {b in the current
      context}. *)

  val subset : ?strict:bool -> t -> t -> bool
  (** [subset ?strict u1 u2] returns [true] if [u1] is a subset of [u2] {b in
      the current context}. [subset] ignores all explanations.

      If set, the [strict] flag ([false] by default) checks for strict
      inclusion. *)

  val equal : t -> t -> bool
  (** [equal u1 u2] returns [true] if [u1] is equal to [u2] {b in the current
      context}. [equal] ignores all explanations. *)

  (** {1 Set manipulation} *)

  val add_explanation : ex:explanation -> t -> t
  (** [add_explanation ~ex u] adds the explanation [ex] to the union [u].

      More precisely: [add_explanation ~ex u] is equivalent to [u] in models
      where [ex] holds, and is [Interval.full] otherwise. *)

  val intersect : t -> t -> (t, explanation) kind
  (** [intersect u1 u2] computes the intersection of [u1] and [u2].

      The resulting intersection is valid in all models. *)

  (** {1 Image by monotone functions}

      The following functions can compute the image of an union by monotone
      function on bounds. *)

  val map_strict_inc : ('a -> bnd) -> 'a union -> t
  (** [map_strict_inc f u] computes the image of [u] by the {b strictly
      increasing} function [f].

      This function is very efficient and should be used when possible. *)

  val map_strict_dec : ('a -> bnd) -> 'a union -> t
  (** [map_strict_dec f u] computes the image of [u] by the {b strictly
      decreasing} function [f].

      This function is very efficient and should be used when possible. *)

  val partial_map_inc :
    ('a -> bnd) -> ('a -> bnd) -> 'a union -> (t, explanation) kind
  (** [partial_map_inc f_lb f_ub u] computes the image of [u] by a partial
      (weakly) increasing function [f].

      [f] is represented by the pair [(f_lb, f_ub)] of functions that are such
      that for any [x], [f_lb x = f x = f_ub x] if [x] is in the domain of
      [f], and [f_ub x < f_lb x] otherwise.

      {b Warning}: The functions [f_lb] and [f_ub] must themselve be (weakly)
      increasing. Moreover, the inequality [f_ub x <= f_lb x] must hold
      everywhere; if [f_lb] and [f_ub] are imprecise approximations of [f], use
      {!approx_map_inc_to_set} instead. *)

  val partial_map_dec :
    ('a -> bnd) -> ('a -> bnd) -> 'a union -> (t, explanation) kind
  (** [partial_map_dec f_lb f_ub u] computes the image of [u] by a partial
      (weakly) decreasing function [f].

      [f] is represented by the pair [(f_lb, f_ub)] of functions that are such
      that for any [x], [f_lb x = f x = f_ub x] if [x] is in the domain of
      [f], and [f_ub x < f_lb x] otherwise.

      {b Warning}: The functions [f_lb] and [f_ub] must themselve be (weakly)
      decreasing. Moreover, the inequality [f_ub x <= f_lb x] must hold
      everywhere; if [f_lb] and [f_ub] are imprecise approximations of [f], use
      {!approx_map_dec_to_set} instead. *)

  (** {1 Image by arbitrary functions}

      When computing the image of an union by non-monotone functions and
      multi-variate functions, work needs to be done to convert intermediate
      results into a normalized form of disjoint intervals (because applying the
      function to initially disjoint intervals can create arbitrary unions).

      In such cases, the following family of [to_set] functions should be used.
      The use the [set] type to represent intermediate results, which can be
      converted back to an union using the [of_set] family of functions as
      needed. *)

  type set
  (** The [set] type represents a (possibly empty) set of intervals.

      Unlike an [union], it is not normalized: it is an intermediate type not
      intended to be manipulated directly, except in the process of building an
      union. Use the [of_set] family of functions to convert it to an union as
      needed. *)

  val empty_set : set
  (** [empty_set] represents an empty set of intervals. *)

  val interval_set : bnd interval -> set
  (** [interval_set i] represents the interval [i] as a [set]. *)

  val union_set : set -> set -> set
  (** [union_set f1 f2] computes the union of the sets of intervals represented
      by [f1] and [f2]. *)

  val map_set : (bnd interval -> bnd interval) -> set -> set
  (** [map_set f s] applies the function [f] to all the intervals in [s]. *)

  val of_set_checked : set -> (t, explanation) kind
  (** Converts a [set] to a nonempty union. Returns [Empty ex] if the set is
      currently empty, and [NonEmpty u] otherwise.

      If a [NonEmpty] value is returned, the resulting union is guaranteed to be
      nonempty in the current context. *)

  val of_set_nonempty : set -> t
  (** Converts a [set] to an union, assuming that it is nonempty in the current
      context.

      @raise Invalid_argument if the [set] represents an union that is empty in
      the current context. *)

  val map_to_set : ('a interval -> set) -> 'a union -> set
  (** [map_to_set f u] computes the image of [u] by [f].

      Conceptually, this computes the union of [f x] for each [x] in [u],
      although this is not possible to compute when [u] might not be finite.
      Instead, we represent [f] by a function from intervals to sets that must
      be isotone (i.e. monotone with respect to inclusion):

      {math I_1 \subseteq I_2 \Rightarrow f(I_1) \subseteq f(I_2)}

      There are no restrictions on [f] (except that it be isotone), which means
      that [map_to_set] needs to call [f] on currently allowed intervals, but
      also on some intervals that are currently impossible but would be possible
      in other contexts (depending on explanations).

      When possible, prefer using a more specialized variant of
      [map_to_set] that use properties of the function [f] to avoid
      certain calls to [f]. *)

  val map_mon_to_set : ('a interval -> set) -> 'a union -> set
  (** [map_mon_to_set] is a variant of [map_to_set] when the
      function [f] is monotone.

      More precisely, we require that for any pair of intervals [(i1, i2)] the
      interval hull of [f i1] and [f i2] is included in the image of the
      interval hull of [i1] and [i2] by [f].

      It is often more convenient to use [approx_map_inc_to_set] or
      [approx_map_dec_to_set] instead, to lift a function on values to a
      function on unions without going through intervals. *)

  val approx_map_inc_to_set : ('a -> bnd) -> ('a -> bnd) -> 'a union -> set
  (** [approx_map_inc_to_set f_lb f_ub u] is a variant of [map_to_set] that is
      appropriate for (weakly) increasing functions.

      The (weakly) increasing function [f] is represented by a pair
      [(f_lb, f_ub)] of functions such that for all [x] in the domain of [f],
      [f_lb x <= f x <= f_ub x] (and [f_ub x < f_lb x] otherwise).

      Note that, unlike [partial_map_inc], this function can be used with
      imprecise approximations: we allow [f_lb x < f x < f_ub x] (this is useful
      for radicals). *)

  val approx_map_dec_to_set : ('a -> bnd) -> ('a -> bnd) -> 'a union -> set
  (** [approx_map_inc_to_set f_lb f_ub u] is a variant of [map_to_set] that is
      appropriate for (weakly) decreasing functions.

      The (weakly) decreasing function [f] is represented by a pair
      [(f_lb, f_ub)] of functions such that for all [x] in the domain of [f],
      [f_lb x <= f x <= f_ub x] (and [f_ub x < f_lb x] otherwise).

      Note that, unlike [partial_map_dec], this function can be used with
      imprecise approximations: we allow [f_lb x < f x < f_ub x]. *)

  val map_inc_to_set : ('a -> bnd) -> 'a union -> set
  (** [map_inc_to_set f u] is a variant of [approx_map_inc_to_set] when the
      underlying function is total and precisely known.

      See also {!map_strict_inc}.

      Note that strict monotony is {b not} required for [map_inc_to_set]. *)

  val map_dec_to_set : ('a -> bnd) -> 'a union -> set
  (** [map_dec_to_set f u] is a variant of [approx_map_dec_to_set] when the
      underlying function is total and precisely known.

      See also {!map_strict_dec}.

      Note that strict monotony is {b not} required for [map_dec_to_set]. *)

  val trisection_map_to_set :
    bnd -> t -> (t -> set) -> (unit -> set) -> (t -> set) -> set
    (** [trisection_map_to_set v u f_lt f_eq f_gt] constructs an union of
        intervals by combining the image of [f_lt] on the fragment of [u] that
        only contains values strictly less than [v], the image of [f_gt] on the
        fragment of [u] that only contains values strictly greater than [v], and
        the image of [f_eq] if [v] is contained in [u].

        It is helpful to build piecewise monotone functions such as
        multiplication, where trisection around [0] can be used. *)
end

(** Polymorphic {!module-type-Union} implementations. *)
module type Core = sig
  type explanation
  (** The type of explanations. *)

  type 'a union
  (** Normalized non-empty union of intervals over ['a] values. *)

  module Union(OT : OrderedType) : Union
    with type 'a union = 'a union
     and type value := OT.finite
     and type bnd = OT.t
     and type explanation := explanation
end

module type RingType = sig
  (** An ordered ring is an ordered type with addition and multiplication that
      follows ring laws. *)

  include OrderedType

  val add : t -> t -> t
  (** [add] will only be called with values that are compatible with its
      monotonicity: its argument can never be two bounds of different kinds
      (upper or lower). *)

  val zero : t
  (** Neutral element for addition. *)

  val neg : t -> t
  (** Inverse for addition: for all [u], [add u (neg u) = zero]. *)

  val mul : t -> t -> t
  (** [mul] will be only be called with values that are compatible with
      its monotonicity: its arguments can be two bounds with the same sign
      and kind (upper or lower), or two bounds with opposite signs and
      opposite kinds (upper or lower), but never two bounds with the same
      sign and opposite kinds or opposite signs and the same kind.

      It is recommended to program defensively and raise an assertion
      failure if [mul] is ever called with two bounds of the same sign and
      opposite kinds or opposite signs and the same kind. *)

  val pow : int -> t -> t
  (** [pow n x] raises [x] to the [n]-th power.

      @raise Invalid_arg if [n] is nonpositive. *)
end

(** Union-of-intervals over a {!RingType}. *)
module type Ring = sig
  include Union (** @inline *)

  (** {1 Ring interface} *)

  val neg : t -> t
  (** [neg u] evaluates to {m \{ -x \mid x \in S \}} when [u] evaluates to
      {m S}. *)

  val add : t -> t -> t
  (** [add u1 u2] evaluates to {m \{ x + y \mid x \in S_1, y \in S_2 \}} when
      [u1] evaluates to {m S_1} and [u2] evaluates to {m S_2}. *)

  val sub : t -> t -> t
  (** [sub u1 u2] evaluates to {m \{ x - y \mid x \in S_1, y \in S_2 \}} when
      [u1] evaluates to {m S_1} and [u2] evaluates to {m S_2}. *)

  val scale : value -> t -> t
  (** [scale v u] evaluates to {m \{ v \times x \mid x \in S \}} when [u]
      evaluates to {m S}.

      @raise Invalid_argument if [v] is zero. *)

  val mul : t -> t -> t
  (** [mul u1 u2] evaluates to {m \{ x \times y \mid x \in S_1, y \in S_2 \}}
      when [u1] evaluates to {m S_1} and [u2] evaluates to {m S_2}. *)

  val pow : int -> t -> t
  (** [pow n u] evaluates to {m \{ x^n \mid x \in S \}} when [u] evaluates to
      {m S}.

      @raise Invalid_argument if [n] is nonpositive. *)
end

module type FieldType = sig
  (** An ordered field type is an ordered ring type equipped with a
      multiplicative inverse. *)

  include RingType

  val inv : t -> t
  (** Inverse for multiplication: for all [u], [mul u (inv u) = one].

      [inv zero] is undefined. *)
end

(** Union-of-intervals over a {!FieldType}. *)
module type Field = sig
  include Ring (** @inline *)

  (** {1 Field interface} *)

  val inv : ?inv0:bnd interval -> t -> t
  (** [inv u] computes the image of [u] by {m x \mapsto x^{-1}}.

      [inv0] is used to define the inverse of [0] and defaults to the full
      interval. *)

  val div : ?inv0:bnd interval -> t -> t -> t
  (** [div u1 u2] computes {m \{ x \times y^{-1} \mid x \in S_1, y \in S_2\}}
      when [u1] evaluates to {m S_1} and [u2] evaluates to {m S_2}.

      [inv0] is used when the divisor can be [0]. It defaults to the full
      interval. *)
end

module type AlgebraicType = sig
  (** An ordered algebraic type is an ordered field with an (approximation of)
      the n-th root. *)

  include FieldType

  val root_default : int -> t -> t
  (** [root_default n x] is an under-approximation of the [n]-th root of [x]. *)

  val root_excess : int -> t -> t
  (** [root_default n x] is an over-approximation of the [n]-th root of [x]. *)
end

(** Union-of-intervals over an {!AlgebraicType}. *)
module type AlgebraicField = sig
  include Field (** @inline *)

  (** {1 Algebraic operations} *)

  val root : int -> t -> (t, explanation) kind
  (** [root n u] computes an over-approximation of the [n]-th root over [u].

      Note that the resulting set can be empty because not all values
      necessarily have a [n]-th root (for instance negative numbers have no real
      square root).

      @raise Invalid_argument if [n] is nonpositive. *)
end

module type EuclideanType = sig
  (** An ordered euclidean type is an ordered ring equipped with an euclidean
      division. *)

  include RingType

  val ediv : t -> t -> t
  (** [ediv x y] returns the euclidean division of [x] by [y].

      @raise Division_by_zero if [y] is [zero]. *)
end

(** Union-of-intervals over an {!EuclideanType}. *)
module type EuclideanRing = sig
  include Ring (** @inline *)

  (** {1 Euclidean division} *)

  val ediv : ?div0:bnd interval -> t -> t -> t
  (** [ediv u1 u2] computes the image of euclidean division of a value in [u1]
      by a value in [u2].

      [div0] (defaults to the full interval) is used as the image of division by
      [zero]. *)
end
