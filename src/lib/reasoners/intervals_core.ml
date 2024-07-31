(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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

open Intervals_intf

(** Pretty-printer for a bound when used as a lower bound. *)
let pp_lower_bound pp_a ppf lb =
  match lb with
  | Unbounded -> Fmt.pf ppf "]-oo"
  | Open x -> Fmt.pf ppf "]%a" pp_a x
  | Closed x -> Fmt.pf ppf "[%a" pp_a x

(** Pretty-printer for a bound when used as an upper bound. *)
let pp_upper_bound pp_a ppf ub =
  match ub with
  | Unbounded -> Fmt.pf ppf "+oo["
  | Open x -> Fmt.pf ppf "%a[" pp_a x
  | Closed x -> Fmt.pf ppf "%a]" pp_a x

module EqLtLeNotations(OT : OrderedType) = struct
  (** This module contains convenient redefinitions of [=], [<], [<=], [min] and
      [max] for use with a specific [OrderedType]. *)

  let[@inline always] ( = ) x y = OT.equal x y

  let[@inline always] ( < ) x y = OT.compare x y < 0

  let[@inline always] ( <= ) x y = OT.compare x y <= 0

  let[@inline always] min x y = if x <= y then x else y

  let[@inline always] max x y = if y <= x then x else y
end

module Interval(OT : OrderedType) = struct
  type value = OT.finite

  type bnd = OT.t

  type t = OT.t interval

  let pp ppf i =
    Fmt.pf ppf "@[%a;@ %a@]"
      (pp_lower_bound OT.pp_finite) (OT.view i.lb)
      (pp_upper_bound OT.pp_finite) (OT.view i.ub)

  open EqLtLeNotations(OT)

  let equal i1 i2 =
    i1.lb = i2.lb && i1.ub = i2.ub

  let of_lower_bound = function
    | Unbounded -> OT.minfty
    | Closed b -> OT.finite b
    | Open b -> OT.succ (OT.finite b)

  let of_upper_bound = function
    | Unbounded -> OT.pinfty
    | Closed b -> OT.finite b
    | Open b -> OT.pred (OT.finite b)

  let of_bounds lb ub =
    let lb = of_lower_bound lb in
    let ub = of_upper_bound ub in
    if ub < lb then invalid_arg "of_bounds"
    else { lb ; ub }

  let view { lb ; ub } = { lb = OT.view lb ; ub = OT.view ub }

  let singleton v = of_bounds (Closed v) (Closed v)

  let full = of_bounds Unbounded Unbounded

  let value_opt { lb ; ub } =
    if lb = ub then OT.value_opt lb else None
end

module Make(Ex : Explanations) : Core with type explanation = Ex.t = struct
  (* This module implements the core functionality of the union-of-intervals
     representation.

     It is the only module that knows about the details of the internal
     representation of the [union] type; all other modules only use the API
     exposed through the [Core] signature.

     As such, its correction is critical to the correction of the implementation
     as a whole; unfortunately, it is also where most of the complexity lies.

     The implementation is actually contained in the [Union] functor; the [Core]
     module itself only contain (polymorphic) type definitions to be able to
     convert values between [Union]s of different types. *)

  type explanation = Ex.t

  type 'a union = 'a * ('a interval, Ex.t) kind list * 'a
  (* We represent intervals as a list of maximal disjoint allowed intervals with
     precise bounds and explanations justifying that the (nonempty) gaps between
     each consecutive allowed interval is forbidden.

     See the definition of the [basic] type below for a discussion on what is
     meant by "allowed" and "forbidden" intervals.

     Note that we do not enforce strict alternance of [Empty] and [NonEmpty]
     intervals; in particular, we allow two consecutive [NonEmpty] intervals if
     the gap between them is always forbidden (i.e. forbidden with explanation
     [Ex.empty]). This allows the module to be (almost) as efficient as an
     implementation without explanations if no explanation is used.

     Moreover, the first and last elements in the list can be either [Empty] or
     [NonEmpty], depending on whether the lower bound (resp. upper) is true
     everywhere (e.g. it is an infinite) or due to an explanation.

     This induces a loss of precision: for instance, if [0, 4] and [10, 20] are
     allowed and [6, 7] is forbidden with justification [ex], this will "widen"
     the forbidden interval to [4+eps, 10-eps] instead; if we find that the
     associated value must be equal to [5], we will include [ex] in the conflict
     even though it is not strictly necessary. On the other hand, there are
     diminishing returns: we don't want to keep track too precisely of the
     forbidden intervals if they are not going to occur in a conflict, because
     they are only used if they are part of a conflict.

     Note that this is always sound, because it is equivalent to adding
     explanations to forbidden intervals (if {m I} is impossible in any model
     where {m e} holds, it is also impossible in any model where {b both} {m e}
     and {m e'} hold). It also does not change the evaluation in the current
     context: we keep track of the bounds of allowed intervals precisely.

     We also store global lower and upper bounds for the union that are always
     valid. This is useful for the [trisection_map_to_set] function to
     communicate information about the range of values to its arguments.

     A note on implementation: many functions in this module that operate on
     unions are written in a somewhat convoluted style where we accumulate an
     [ex] argument representing a forbidden interval. The idea is that we are
     accumulating all the [Empty] forbidden intervals until the next [NonEmpty]
     allowed interval (or the end of the union), at which point we deal with
     both the [NonEmpty] allowed interval and its (virtual) [Empty] allowed
     prefix. This allows to minimize the number of cases to take into
     consideration (union starting/ending with [Empty] or [NonEmpty], union that
     contains exactly one [Empty] and one [NonEmpty], elided [Empty] between two
     consecutive [NonEmpty], etc.).

     In practice, I (the original author of this module) tried many different
     styles (such as encoding invariants in GADTs or polymorphic variants,
     strengthening the invariants, iterating over consecutive pairs of elements)
     and found that this style, while a bit awkward initially, was the one that
     was the most robust to accidental soundness bugs. *)

  module Union(OT : OrderedType) = struct
    module Interval = Interval(OT)

    open EqLtLeNotations(OT)

    type nonrec 'a union = 'a union

    type bnd = OT.t

    type t = OT.t union

    let pp ppf (glb, u, gub) =
      let rec loop ex = function
        | Empty ex' :: u' -> loop (Ex.union ex ex') u'
        | [] ->
          if Ex.is_empty ex then ()
          else Fmt.pf ppf "!%a (<= %a)" Ex.pp ex OT.pp gub
        | NonEmpty i :: u' ->
          if not (Ex.is_empty ex) then Fmt.pf ppf "!%a U@ " Ex.pp ex;
          Interval.pp ppf i;
          if not (Compat.List.is_empty u') then Fmt.pf ppf " U@ ";
          loop ex u'
      in
      begin match u with
        | NonEmpty _ :: _ -> ()
        | _ -> Fmt.pf ppf "(%a <=)@ " OT.pp glb
      end;
      loop Ex.empty u

    let pp = Fmt.box pp

    (** {2 Creation} *)

    let of_interval ?(ex = Ex.empty) i =
      if Ex.is_empty ex then
        (i.lb, [ NonEmpty i ], i.ub)
      else
        let u = if i.ub = OT.pinfty then [] else [ Empty ex ] in
        let u = NonEmpty i :: u in
        let u = if i.lb = OT.minfty then u else Empty ex :: u in
        (OT.minfty, u, OT.pinfty)

    let[@inline always] of_bounds ?ex lb ub =
      of_interval ?ex @@ Interval.of_bounds lb ub

    let empty ex u =
      if Ex.is_empty ex then u else Empty ex :: u

    let of_complement ?(ex = Ex.empty) i =
      if i.ub = OT.pinfty then
        if i.lb = OT.minfty then
          Empty ex
        else
          NonEmpty (
            let u =
              NonEmpty { lb = OT.minfty ; ub = OT.pred i.lb } :: empty ex []
            in
            (OT.minfty, u, OT.pinfty)
          )
      else
        NonEmpty (
          let u = empty ex [NonEmpty { lb = OT.succ i.ub ; ub = OT.pinfty }] in
          let u =
            if i.lb = OT.minfty then u
            else NonEmpty { lb = OT.minfty ; ub = OT.pred i.lb } :: u
          in
          (OT.minfty, u, OT.pinfty)
        )

    (** {2 Inspection} *)

    let lower_bound (_, u, _) =
      let rec lower_bound ex = function
        | [] -> invalid_arg "lower_bound: empty union"
        | NonEmpty i :: _ -> OT.view i.lb, ex
        | Empty ex' :: u -> lower_bound (Ex.union ex ex') u
      in lower_bound Ex.empty u

    let upper_bound (_, u, _) =
      let rec upper_bound ub ex = function
        | [] -> OT.view ub, ex
        | Empty ex' :: u -> upper_bound ub (Ex.union ex ex') u
        | NonEmpty i :: u -> upper_bound i.ub Ex.empty u
      in
      let rec init = function
        | [] -> invalid_arg "upper_bound: empty union"
        | Empty _ :: u -> init u
        | NonEmpty i :: u -> upper_bound i.ub Ex.empty u
      in
      init u

    let value_opt (_, u, _) =
      let rec loop ex v = function
        | Empty ex' :: u -> loop (Ex.union ex ex') v u
        | [] -> Option.map (fun v -> (v, ex)) v
        | NonEmpty i :: u ->
          match v with
          | None when i.lb = i.ub -> loop ex (OT.value_opt i.lb) u
          | _ -> None
      in loop Ex.empty None u

    (** {2 Iteration} *)

    let to_seq (_, u, _) =
      List.to_seq u |> Seq.filter_map (function
          | NonEmpty i -> Some i
          | Empty _ -> None)

    let fold f acc (_, u, _) =
      List.fold_left (fun acc -> function
          | NonEmpty i -> f acc i
          | Empty _ -> acc
        ) acc u

    let iter f (_, u, _) =
      List.iter (function
          | NonEmpty i -> f i
          | Empty _ -> ()
        ) u

    (** {2 Comparison} *)

    (* Note: [subset] and [equal] could be implemented outside of this module as
       they do not deal with explanations. There are the exception to the rule
       that only functions related to explanations are implemented in [Union],
       because it just makes sense to have them here. *)

    let rec subset_seq ~strict i1 s1 i2 s2 =
      if i2.ub < i1.lb then
        (* i1 is entirely after i2; skip i2
           NB: we never need (i1 U s1) to be a strict subset of s2 because i2 is
           in (i2 U s2) but not in (i1 U s1), making the inclusion strict. *)
        match Compat.Seq.uncons s2 with
        | None -> false
        | Some (i2', s2') -> subset_seq ~strict:false i1 s1 i2' s2'
      else
        i2.lb <= i1.lb && i1.ub <= i2.ub &&
        let strict = strict && i1.lb = i2.lb && i1.ub = i2.ub in
        match Compat.Seq.uncons s1 with
        | None -> not strict || Option.is_some (Compat.Seq.uncons s2)
        | Some (i1', s1') ->
          if strict then
            match Compat.Seq.uncons s2 with
            | None -> false
            | Some (i2', s2') -> subset_seq ~strict:true i1' s1' i2' s2'
          else
            subset_seq ~strict:false i1' s1' i2 s2

    let subset ?(strict = false) u1 u2 =
      let uncons = Compat.Seq.uncons in
      match uncons (to_seq u1), uncons (to_seq u2) with
      | None, None -> not strict
      | Some _, None -> false
      | None, Some _ -> true
      | Some (i1, s1), Some (i2, s2) ->
        subset_seq ~strict i1 s1 i2 s2

    let equal u1 u2 =
      Compat.Seq.equal Interval.equal (to_seq u1) (to_seq u2)

    let checked ((glb, u', gub) as u) =
      let rec loop ex = function
        | Empty ex' :: u' -> loop (Ex.union ex ex') u'
        | [] -> Empty ex
        | NonEmpty _ :: _ -> NonEmpty u
      in
      if gub < glb then Empty Ex.empty else loop Ex.empty u'

    let nonempty = function
      | NonEmpty u -> u
      | Empty _ -> invalid_arg "nonempty"

    let checked_opt = function
      | None -> Empty Ex.empty
      | Some u -> checked u

    let add_explanation ~ex:global_ex ((_, u, _) as u') =
      if Ex.is_empty global_ex then u'
      else
        let[@tail_mod_cons] rec loop ex = function
          | Empty ex' :: u -> loop (Ex.union ex ex') u
          | [] -> [ Empty ex ]
          | [ NonEmpty i ] as u when i.ub = OT.pinfty -> Empty ex :: u
          | NonEmpty i :: u -> Empty ex :: NonEmpty i :: loop global_ex u
        in
        let u =
          match u with
          | NonEmpty i :: u when i.lb = OT.minfty ->
            if i.ub = OT.pinfty then [ NonEmpty i ]
            else NonEmpty i :: loop global_ex u
          | _ -> loop global_ex u
        in
        (OT.minfty, u, OT.pinfty)

    let min_ex ex1 ex2 =
      if Stdlib.(Ex.compare ex1 ex2 <= 0) then ex1 else ex2

    (* Computing the intersection follows a fairly natural, if a bit tedious,
       process: we are simply iterating on the two unions at the same time and
       computing the intersections as we go.

       Some care need to be taken of to make sure to use appropriate
       explanations. When one of the unions is enough to forbid a given
       forbidden interval, we only want to use that one (for instance, the
       intersection of [-oo; 4] with explanation [ex1] and [-oo; 10] with
       explanation [ex2] only needs explanation [ex1]). We only need to take the
       union of the explanations when the explanation in one union is used to
       skip over an interval that was allowed in the other union; for instance,
       the intersection of

        [0; 1] U !ex1 U [2; 3]

       and

        !ex2 U [4; 10]

       must be

        !(union ex1 ex2) U [2; 3]

       We need [ex1] to forbid ]1; 2[ and [ex2] to forbid [0; 1] and [2; 4].

       In addition, the current implementation respects the known global
       lower/upper bounds, which adds a low amount of complexity (everything
       before/after the global lower/upper bound can be removed without
       justification). An alternative implementation could ignore the global
       lower and upper bounds and always return [-oo, +oo] as an enclosing
       interval; which might improve efficiency of further computations. *)
    let intersect =
      let[@tail_mod_cons] rec loop ex1 u1 ex2 u2 gub =
        match u1, u2 with
        | [], [] -> (empty [@tailcall false]) (min_ex ex1 ex2) []
        | Empty ex1' :: u1', _ -> loop (Ex.union ex1 ex1') u1' ex2 u2 gub
        | _, Empty ex2' :: u2' -> loop ex1 u1 (Ex.union ex2 ex2') u2' gub
        | NonEmpty i1 :: _, _ when gub < i1.lb -> loop ex1 [] ex2 u2 gub
        | _, NonEmpty i2 :: _ when gub < i2.lb -> loop ex1 u1 ex2 [] gub
        | [], NonEmpty _ :: _ -> (empty [@tailcall false]) ex1 []
        | NonEmpty _ :: _, [] -> (empty [@tailcall false]) ex2 []
        | NonEmpty i1 :: u1', NonEmpty i2 :: u2' ->
          let i1, u1' =
            if gub < i1.ub then { i1 with ub = gub }, [] else i1, u1'
          and i2, u2' =
            if gub < i2.ub then { i2 with ub = gub }, [] else i2, u2'
          in
          if i2.ub < i1.lb then loop ex1 u1 (Ex.union ex1 ex2) u2' gub
          else if i1.ub < i2.lb then loop (Ex.union ex1 ex2) u1' ex2 u2 gub
          else
            let ub = min i1.ub i2.ub in
            let lb, ex =
              if i1.lb < i2.lb then i2.lb, ex2
              else if i2.lb < i1.lb then i1.lb, ex1
              else i1.lb, min_ex ex1 ex2
            in
            if Ex.is_empty ex then cons_loop { lb ; ub } i1 u1' i2 u2' gub
            else Empty ex :: cons_loop { lb ; ub } i1 u1' i2 u2' gub
      and[@tail_mod_cons] cons_loop i i1 u1 i2 u2 gub =
        NonEmpty i ::
        let lb = OT.succ i.ub in
        let u1' = if i.ub < i1.ub then NonEmpty { i1 with lb } :: u1 else u1 in
        let u2' = if i.ub < i2.ub then NonEmpty { i2 with lb } :: u2 else u2 in
        loop Ex.empty u1' Ex.empty u2' gub
      in
      fun (glb1, u1, gub1) (glb2, u2, gub2) ->
        let glb = max glb1 glb2 and gub = min gub1 gub2 in
        if gub < glb then Empty Ex.empty else
          let rec gist_ge glb ex = function
            | [] -> empty ex []
            | Empty ex' :: u' -> gist_ge glb (Ex.union ex ex') u'
            | NonEmpty i :: u' when i.ub < glb -> gist_ge glb Ex.empty u'
            | NonEmpty i :: u' as u ->
              if glb < i.lb then empty ex u
              else NonEmpty { i with lb = glb } :: u'
          in
          let u1 = gist_ge glb Ex.empty u1 and u2 = gist_ge glb Ex.empty u2 in
          checked (glb, loop Ex.empty u1 Ex.empty u2 gub, gub)

    (** {2 Image by monotone functions} *)

    (* Note that [partial_map_inc] and [partial_map_dec] are currently
       implemented in the next section using [approx_map_inc_to_set] and
       [approx_map_dec_to_set] for simplicity. *)

    let map_strict_inc f (glb, u, gub) =
      (* Use a [ref] here instead of returning a pair to allow [@tail_mod_cons]
         annotation in [loop]. *)
      let f_gub = ref None in
      let[@tail_mod_cons] rec loop = function
        | [] -> []
        | Empty ex :: u' -> Empty ex :: loop u'
        | NonEmpty i :: u' ->
          let f_i = { lb = f i.lb ; ub = f i.ub } in
          if Compat.List.is_empty u' then f_gub := Some f_i.ub;
          NonEmpty f_i :: loop u'
      in
      let f_u = loop u in
      let f_glb = match f_u with NonEmpty i :: _ -> i.lb | _ -> f glb in
      let f_gub = match !f_gub with Some gub -> gub | None -> f gub in
      (f_glb, f_u, f_gub)

    let map_strict_dec f (glb, u, gub) =
      let rec loop f_glb acc = function
        | [] -> (f gub, acc, f_glb)
        | Empty ex' :: u' -> loop f_glb (Empty ex' :: acc) u'
        | NonEmpty i :: u' ->
          let f_i = { lb = f i.ub ; ub = f i.lb } in
          loop f_glb (NonEmpty f_i :: acc) u'
      in
      let init = function
        | NonEmpty i :: u' ->
          let f_i = { lb = f i.ub ; ub = f i.lb } in
          loop f_i.ub [NonEmpty f_i] u'
        | u -> loop (f glb) [] u
      in init u

    (** {2 Image by arbitrary functions} *)

    type basic =
      | Allow of OT.t interval
      | Forbid of OT.t interval * Ex.t
      (* An allowed interval, represented by the [Allow] constructor, is an
         interval that is possible in all contexts (i.e. we do not have any
         proof that the values in this interval are impossible).

         A forbidden interval, represented by the [Forbid] constructor, is an
         interval that is possible in contexts where the associated explanation
         is *false*; moreover, the associated explanation must be *true* in the
         *current context.

         A forbidden interval says *nothing* about the corresponding values in
         contexts where the associated explanation is true, such as the current
         context. This means that:

         - In an union, any value that is allowed is possible in all contexts,
           and any value that is not allowed is possible in contexts where
           *either* of the explanations that forbid it is false. This means that
           we must take the union of all explanations that apply to a given
           forbidden value: say that [v] is forbidden by [e1] or (union) by
           [e2].  If we were only keeping the information that it is forbidden
           by [e1], discarding [e2], then we would think it is not possible in
           contexts where [e1] is [true] but [e2] is [false].

           Mathematically:

           {math
             (M(e_1) \Rightarrow M(x) \neq v)
             \vee
             (M(e_2) \Rightarrow M(x) \neq v)
             \Longleftrightarrow
             (M(e_1) \wedge M(e_2) \Rightarrow M(x) \neq v)
           }

           We cannot weaken here, because neither {m M(e_1)} nor {m M(e_2)}
           implies {m M(e_1) \wedge M(e_2)}.

         - In an intersection, a value that is allowed in *all* members of the
           intersection is possible in all contexts. On the other hand, it is
           enough to keep any of the forbidding explanations: say that [v] is
           forbidden by [e1] and (intersection) [e2]. It is enough to keep the
           information that it is forbidden by [e1], discarding [e2]: there are
           no contexts where [e1] is [true] but [v] is possible.

           Mathematically:

           {math
             (M(e_1) \Rightarrow M(x) \neq v)
               \wedge
             (M(e_2) \Rightarrow M(x) \neq v)

             \Longleftrightarrow

             (M(e_1) \vee M(e_2) \Rightarrow M(x) \neq v)
           }

           We can weaken to either [e1] or [e2] here, because both {m M(e_1)}
           and {m M(e_2)} imply {m M(e_1) \vee M(e_2)}. *)

    (* The [set] type represents a loose union of [basic] intervals. There
       are no restrictions on the underlying [basic] intervals (although they
       should be valid, as per the {!Intervals} signature).

       Because we mostly use the [set] type as an intermediate accumulator when
       building unions, we expose it as functions from list of [basic] intervals
       to [basic] intervals. The underlying list can be recovered by calling the
       [set] with an empty list as argument, and we will loosely identify the
       [set] and its representation as a list. *)

    type set = basic list -> basic list

    let empty_set = fun acc -> acc

    let interval_set i acc = Allow i :: acc

    let union_set s1 s2 acc = s1 (s2 acc)

    let map_set f s acc =
      (* Make sure to only call [f] on the intervals that come from [s]! *)
      List.rev_append (
        List.rev_map (function
            | Allow i -> Allow (f i)
            | Forbid (i, ex) -> Forbid (f i, ex)
          ) (s [])
      ) acc

    let of_set =
      (* [of_set] is used to convert an unnormalized [set] to a normalized
         [union]. Since a [set] can be empty, but an [union] cannot, we return
         an [option] here.

         We maintain a list of the [basic] sets, sorted by decreasing upper
         bound (it would be more natural to sort by increasing lower bound, but
         sorting by decreasing upper bound allows us to build the resulting
         [union] backwards in a tail-recursive way). *)

      (* [prepend_forbid gub lb u] is used to add all the forbidden intervals
         from [fs] to the initial segment before [u].

         [u] must begin with an allowed segment that starts at [lb]; any
         forbidden intervals that start at [lb] or after can be skipped. *)
      let rec prepend_forbid gub lb u = function
        | [] -> (lb, u, gub)
        | (flb, _) :: fs when lb <= flb ->
          prepend_forbid gub lb u fs
        | (glb, ex) :: fs ->
          let glb, ex =
            List.fold_left (fun (glb, ex) (lb', ex') ->
                if lb <= lb' then (glb, ex) else (min glb lb', Ex.union ex ex')
              ) (glb, ex) fs
          in
          (glb, Empty ex :: u, gub)
      in
      (* Main loop.

         We assume the input list to be sorted by decreasing upper bound, and
         the upper bound of intervals in the input list are currently [<= ub].

         We have built the union [u], and are processing an allowed interval
         { lb ; ub } to be added at the start of [u]. We don't add it yet,
         because it may need to be merged with other allowed intervals we have
         not processed yet: we have only processed intervals with an upper bound
         greater than or equal to [ub], but there may be allowed intervals that
         end inside [lb; ub] (or at [pred lb]).

         Recall that a value is allowed as soon as it is part of an allowed
         interval, but to be forbidden it must be part of no allowed interval
         and is forbidden by the union of all explanations associated with
         forbidden intervals that contains it.

         The list [fs] collects a set of forbidden half-intervals that must be
         added before [lb; ub] (unless they get subsumed by merging). *)
      let rec loop gub lb ub u fs = function
        | [] ->
          prepend_forbid gub lb (NonEmpty { lb ; ub } :: u) fs
        | Forbid (i, _) :: s when lb <= i.lb ->
          (* [i] is subsumed by [lb; ub], which is allowed.

                    lb ___________________ ub
                    /                     \
             -oo -----|AAAAAA|AAAAAAAA|AAAAA|--------> +oo
                            \________/
                                i
          *)
          loop gub lb ub u fs s
        | Forbid (i, ex) :: s ->
          (* [i] starts before [lb]; need to keep it

                          lb _____________ ub
                            /              \
             -oo -----|??????|AAAAAAAAAAAAAA|--------> +oo
                     \___...
                       i

             NB: [i.ub] might also be before [lb], in which case we weaken. *)
          loop gub lb ub u ((i.lb, ex) :: fs) s
        | Allow i :: s when lb <= i.ub || OT.succ i.ub = lb ->
          (* No gap: merge intervals ([i.ub] is smaller by sorting)

                          lb _____________ ub
                            /              \
             -oo -----|AAAAAA|AAAAAAAAAAAAAA|--------> +oo
                     \____________/
                            i

                   lb _____________________ ub
                     /                     \
             -oo -----|AAAAAAAAAAAAAAAAAAAAA|--------> +oo
                         \________/
                             i
          *)
          loop gub (min i.lb lb) ub u fs s
        | Allow i :: s ->
          (* Gap with another allowed interval

                                lb _______ ub
                                  /        \
             -oo -----|AAAAAA|FFFF|AAAAAAAAA|--------> +oo
                     \______/
                        i

             NB: Look into the forbidden half-intervals in [fs] to determine the
             explanation for the gap. *)
          assert (OT.succ i.ub < lb);
          (* Need to filter the [flb] again because the forbidden intervals
             might have been added before the merging that subsumed it. *)
          let ex =
            List.fold_left (fun ex (flb, ex') ->
                if flb < lb then Ex.union ex ex' else ex
              ) Ex.empty fs
          in
          let forbid = List.filter (fun (flb, _) -> flb < i.lb) fs in
          let u = empty ex @@ NonEmpty { lb ; ub } :: u in
          loop gub i.lb i.ub u forbid s
      in
      (* Look for the first allowed interval (which has the highest upper bound,
         since the input list is sorted by decreasing order).

         Note that we assume that ties are broken by sorting allowed intervals
         before forbidden intervals. *)
      let rec init lb ex gub fs = function
        | [] -> (lb, [ Empty ex ], gub)
        | Allow i :: s ->
          assert (i.ub < gub);
          let fs = List.filter (fun (lb, _) -> lb < i.lb) fs in
          loop gub i.lb i.ub [Empty ex] fs s
        | Forbid (i, ex') :: s ->
          (* NB: all allowed intervals have a strictly smaller upper bound due
             to our tie-breaking. *)
          init (min lb i.lb) (Ex.union ex ex') gub ((i.lb, ex') :: fs) s
      in
      fun s ->
        let s =
          List.filter
            (function Allow _ -> true | Forbid (_, ex) -> not (Ex.is_empty ex))
            (s [])
        in
        (* Sort by decreasing upper bound, ties going to allowed intervals *)
        let rev_cmp b1 b2 =
          let (Allow i1 | Forbid (i1, _)) = b1 in
          let (Allow i2 | Forbid (i2, _)) = b2 in
          let c = OT.compare i2.ub i1.ub in
          if c <> 0 then c else
            match b1, b2 with
            | Allow _, Forbid _ -> -1
            | Forbid _, Allow _ -> 1
            | Allow _, Allow _ | Forbid _, Forbid _ -> 0
        in
        match List.fast_sort rev_cmp s with
        | [] -> None
        | Allow i :: s ->
          Some (loop i.ub i.lb i.ub [] [] s)
        | Forbid (i, ex) :: s ->
          (* NB: all allowed intervals have a strictly smaller upper bound due
             to our tie-breaking. *)
          Some (init i.lb ex i.ub [(i.lb, ex)] s)

    let of_set_checked s = checked_opt (of_set s)

    let of_set_nonempty s = nonempty @@ checked_opt @@ of_set s

    let forbid_set ~ex s acc =
      if Ex.is_empty ex then acc
      else
        (* NB: We can ignore the existing explanation from forbidden intervals
           because the interval is forbidden by both explanations.

           This might seem confusing, but recall that an interval is possible if
           the associated explanation is *false*: if both explanations are
           false, then in particular [ex] is false, and we can weaken and make
           the interval possible in any context where only [ex] is false. *)
        List.rev_append
          (List.rev_map
             (function Allow i | Forbid (i, _) -> Forbid (i, ex)) (s []))
          acc

    (* Note that for forbidden intervals we call [f] with a slightly
       larger interval that includes the allowed parts. *)
    let map_to_set f (glb, u, gub) acc =
      let rec loop acc lb ex = function
        | Empty ex' :: u -> loop acc lb (Ex.union ex ex') u
        | [] -> forbid_set ~ex (f { lb ; ub = gub }) acc
        | NonEmpty i :: u ->
          let acc =
            if Ex.is_empty ex then acc
            else forbid_set ~ex (f { i with lb }) acc
          in
          loop (f i acc) i.lb Ex.empty  u
      in loop acc glb Ex.empty u

    let union_hull i1 i2 =
      { lb = min i1.lb i2.lb ; ub = max i1.ub i2.ub }

    (* Compute the convex hull of a set as an interval.
       This is a *global* convex hull: any value in the set *in any context* is
       in the returned interval. *)
    let convex_hull_of_set = function
      | [] -> None
      | (Allow i | Forbid (i, _)) :: s ->
        Some (
          List.fold_left (fun { lb = glb ; ub  = gub } b ->
              let { lb ; ub } = match b with Allow i | Forbid (i, _) -> i in
              { lb = min lb glb ; ub = max ub gub }
            ) i s
        )

    (* Similar to [map_to_set] except that we are keeping track of the
       global convex hull of each call to [f i] where [i] is allowed.

       Then we know that if [x] is between two consecutive intervals
       [i] and [i'] (with [i.ub < i'.lb]), [f x] is included in the
       hull of [union (f i) (f i')].

       Note that we "overflow" from the strict gap between [i] and
       [i'] but that is OK: the image of [f i] and [f i'] are allowed,
       which will subsume the corresponding forbidden part from the
       hulls when converting back to an union. *)
    let map_mon_to_set f (glb, u, gub) acc =
      let rec loop acc prev_hull lb ex = function
        | Empty ex' :: u -> loop acc prev_hull lb (Ex.union ex ex') u
        | [] -> forbid_set ~ex (f { lb ; ub = gub }) acc
        | NonEmpty i :: u ->
          let f_i = f i [] in
          match convex_hull_of_set f_i with
          | None -> loop acc prev_hull lb ex u
          | Some hull_f ->
            let acc =
              if Ex.is_empty ex then acc
              else Forbid (union_hull prev_hull hull_f, ex) :: acc
            in
            let acc = List.rev_append f_i acc in
            loop acc hull_f i.lb Ex.empty u
      in
      let rec init ex = function
        | [] -> forbid_set ~ex (f { lb = glb ; ub = gub }) acc
        | Empty ex' :: u -> init (Ex.union ex ex') u
        | NonEmpty i :: u ->
          let f_i = f i [] in
          match convex_hull_of_set f_i with
          | None -> init ex u
          | Some hull_f ->
            let acc =
              if Ex.is_empty ex then acc
              else forbid_set ~ex (f { i with lb = glb }) acc
            in
            let acc = List.rev_append f_i acc in
            loop acc hull_f i.lb Ex.empty u
      in init Ex.empty u

    let approx_map_inc_to_set f_lb f_ub u acc =
      map_mon_to_set (fun i ->
          let lb = f_lb i.lb and ub = f_ub i.ub in
          if OT.compare lb ub > 0 then empty_set
          else interval_set { lb ; ub }
        ) u acc

    let approx_map_dec_to_set f_lb f_ub u acc =
      map_mon_to_set (fun i ->
          let ub = f_ub i.lb and lb = f_lb i.ub in
          if OT.compare lb ub > 0 then empty_set
          else interval_set { lb ; ub }
        ) u acc

    let map_inc_to_set f u = approx_map_inc_to_set f f u

    let map_dec_to_set f u = approx_map_dec_to_set f f u

    (* We could generalize [map_strict_inc] and [map_strict_dec] to implement
       [partial_map_inc] and [partial_map_dec] but that would make the code more
       complex due to needing to potentially merge consecutive intervals.
       Instead, we centralize such logic in [of_set] (but still provide the
       [partial_map_inc] and [partial_map_dec] interfaces to be able to switch
       to a specialized implementation later). *)

    let partial_map_inc f_lb f_ub u =
      of_set_checked (approx_map_inc_to_set f_lb f_ub u)

    let partial_map_dec f_lb f_ub u =
      of_set_checked (approx_map_dec_to_set f_lb f_ub u)

    (* [uncons] and [cons] functions provide a convenient "view" of an [union].
       They allow uniform reasoning between allowed and forbidden intervals in
       [trisection_map_to_set]. *)

    (** [uncons u] returns a triple [i, ex, u'] such that [i] is the first
        interval of [u] and [u'] is the part of [u] strictly after [i.ub] if
        any.

        The explanation [ex] is [None] if [i] is allowed, and [Some] with the
        corresponding explanation if [i] is forbidden. *)
    let uncons (glb, u, gub) =
      let rec loop ex = function
        | Empty ex' :: u' -> loop (Ex.union ex ex') u'
        | [] -> { lb = glb ; ub = gub }, Some ex, None
        | NonEmpty i :: u' as u ->
          if Ex.is_empty ex then
            match u' with
            | [] -> (i, None, None)
            | _ -> (i, None, Some (OT.succ i.ub, u', gub))
          else ({ lb = glb ; ub = OT.pred i.lb }, Some ex, Some (i.lb, u, gub))
      in loop Ex.empty u

    (** [cons i ex u] prepends the interval [i] (as an allowed interval if [ex]
        is [None], and a forbidden interval if it is [Some]) to the union [u].

        [u] must start after i, i.e. we must have [i.ub < (hull u).lb].

        [cons] is an inverse of [uncons], but [uncons] is not an inverse of
        [cons] because [cons] can merge consecutive intervals. *)

    let cons i ex u =
      match u with
      | None -> (
          match ex with
          | None-> (i.lb, [ NonEmpty i ], i.ub)
          | Some ex->
            if Ex.is_empty ex then (i.lb, [], i.ub)
            else (i.lb, [ Empty ex ], i.ub)
        )
      | Some (glb, u, gub) ->
        assert (i.ub < glb);
        match ex, u with
        | None, NonEmpty i' :: u' when OT.succ i.ub = i'.lb ->
          (i.lb, NonEmpty { lb = i.lb ; ub = i'.ub } :: u', gub)
        | None, _ -> (i.lb, NonEmpty i :: u, gub)
        | Some ex, Empty ex' :: u' ->
          (i.lb, Empty (Ex.union ex ex') :: u', gub)
        | Some ex, _ -> (i.lb, empty ex u, gub)


    let trisection_map_to_set v ((_, _, gub) as u) f_lt f_eq f_gt acc =
      if gub < v then
        (* Optimization to avoid traversing the whole union *)
        f_lt u acc
      else
        let rec trisection acc u =
          let i, ex, u' = uncons u in
          if i.ub < v then
            (* The interval is strictly before the value *)
            match u' with
            | None ->
              Some (cons i ex None), acc
            | Some u' ->
              let before, acc = trisection acc u' in
              Some (cons i ex before), acc
          else
            (* v <= i.ub *)
            let before =
              (* [before] is the portion of [i] strictly before [v], if any *)
              if v <= i.lb then None
              else Some (cons { i with ub = OT.pred v } ex None)
            in
            let acc =
              (* if [v] is inside [i], add [f_eq] to the mix with appropriate
                 explanation. *)
              if v < i.lb || Option.fold ~none:false ~some:Ex.is_empty ex then
                acc
              else
                match ex with
                | None -> f_eq () acc
                | Some ex -> forbid_set ~ex (f_eq ()) acc
            in
            let after =
              (* [after] is the portion of [u] strictly after [v], if any *)
              if v = i.ub then u'
              else if v < i.lb then Some (cons i ex u')
              else Some (cons { i with lb = OT.succ v } ex u')
            in
            let acc =
              match after with
              | Some after -> f_gt after acc
              | None -> acc
            in
            before, acc
        in
        let before, acc = trisection acc u in
        match before with
        | Some before -> f_lt before acc
        | None -> acc
  end
end
