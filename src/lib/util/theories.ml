(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2023 --- OCamlPro SAS                                *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type prelude = Fpa | Ria | Nra

let fpa_ae = {|
theory Simple_FPA extends FPA =

   (* what happends if we add versions for partially bounded float(x) ?
      whould this be better ? *)

   axiom rounding_operator_1 :
     forall x : real.
     forall i, j : real.
     forall i2, j2 : real.
     forall mode : fpa_rounding_mode.
     forall p, m : int
     [
        float(m, p, mode, x),
        is_theory_constant(m),
        is_theory_constant(p),
        is_theory_constant(mode),
        x in [i, j],
        i2 |-> float(m, p, mode, i),
        j2 |-> float(m, p, mode, j)
     ]
     {
        i <= x,
        x <= j
     }.
     i2 <= float(m, p, mode, x) <= j2


   axiom integer_rounding_operator_1 :
     forall x : real.
     forall i, j : real.
     forall i2, j2 : int.
     forall mode : fpa_rounding_mode
     [
        integer_round(mode, x),
        is_theory_constant(mode),
        x in [i, j],
        i2 |-> integer_round(mode, i),
        j2 |-> integer_round(mode, j)
     ]
     {
        i <= x,
        x <= j
     }.
     i2 <= integer_round(mode, x) <= j2


  (* add the version with x in ? -> o(x) - x in ? *)
  axiom rounding_operator_absolute_error_1_NearestTiesToEven :
     forall x : real.
     forall i, j, k : real.
     forall exp_min, prec : int
     [
        float(prec, exp_min, NearestTiesToEven, x),
        is_theory_constant(prec),
        is_theory_constant(exp_min),
        x in [i, j],
        k |->
           2 **. (
            integer_log2(
              max_real(
                abs_real(i),
                max_real(
                  abs_real(j),
                  2 **. (- exp_min + prec-1)
                )
               )
             ) - prec (* we can improve by -1 for some rounding modes *)
           )
     ]
     {
        i <= x,
        x <= j
     }.
     - k <=  float(prec, exp_min, NearestTiesToEven, x) - x <= k


  axiom rounding_operator_absolute_error_1_ALL :
     forall x : real.
     forall i, j, k : real.
     forall mode : fpa_rounding_mode.
     forall exp_min, prec : int
     [
        float(prec, exp_min, mode, x),
        is_theory_constant(prec),
        is_theory_constant(exp_min),
        is_theory_constant(mode),
        x in [i, j],
        k |->
           2 **. (
            integer_log2(
              max_real(
                abs_real(i),
                max_real(
                  abs_real(j),
                  2 **. (- exp_min + prec-1)
                )
               )
             ) - prec + 1(* we can improve by -1 for some rounding modes *)
           )
     ]
     {
        i <= x,
        x <= j
     }.
     - k <=  float(prec, exp_min, mode, x) - x <= k

   axiom monotonicity_contrapositive_1 :
      forall x, i, k : real.
      forall mode : fpa_rounding_mode.
      forall exp_min, prec : int
      [
         float(prec, exp_min, mode, x),
         is_theory_constant(prec),
         is_theory_constant(exp_min),
         is_theory_constant(mode),
         float(prec, exp_min, mode, x) in [?, i[,
         k |-> float(prec, exp_min, Up, i)
      ]
      {
         float(prec, exp_min, mode, x) < i
      }.
      (*float(prec, exp_min, mode, x) < i ->*)
      x < k


   axiom monotonicity_contrapositive_2 :
      forall x, i, k : real.
      forall mode : fpa_rounding_mode.
      forall exp_min, prec : int
      [
         float(prec, exp_min, mode, x),
         is_theory_constant(prec),
         is_theory_constant(exp_min),
         is_theory_constant(mode),
         float(prec, exp_min, mode, x) in ]i, ?],
         k |-> float(prec, exp_min, Down, i)
      ]
      {
         float(prec, exp_min, mode, x) > i
      }.
      (*float(prec, exp_min, mode, x) > i ->*)
      x > k

   (* Remark: should add semantic trigger 'x <= y'
      or maybe also 'float(m,p,md,x) > float(m,p,md,y)' in future
      version *)
   (* same as old monotonicity_contrapositive_3 *)
   axiom float_is_monotonic:
     forall m, p : int.
     forall md : fpa_rounding_mode.
     forall x, y : real
     [
         float(m,p,md,x), float(m,p,md,y),
         is_theory_constant(m),
         is_theory_constant(p),
         is_theory_constant(md)
     ].
     x <= y -> float(m,p,md,x) <= float(m,p,md,y)


   (* these two axioms are too expensive if put inside a theory *)
   axiom monotonicity_contrapositive_4 :
      forall x, y : real.
      forall mode : fpa_rounding_mode.
      forall exp_min, prec : int
      [
         float(prec, exp_min, mode, x),float(prec, exp_min, mode, y),
         is_theory_constant(prec),
         is_theory_constant(exp_min),
         is_theory_constant(mode)
      ].
      float(prec, exp_min, mode, x) < float(prec, exp_min, mode, y) ->
      x < float(prec, exp_min, mode, y)

   axiom monotonicity_contrapositive_5 :
      forall x, y : real.
      forall mode : fpa_rounding_mode.
      forall exp_min, prec : int
      [
         float(prec, exp_min, mode, x), float(prec, exp_min, mode, y),
         is_theory_constant(prec),
         is_theory_constant(exp_min),
         is_theory_constant(mode)
      ].
      float(prec, exp_min, mode, x) < float(prec, exp_min, mode, y) ->
      float(prec, exp_min, mode, x) < y


   axiom contrapositive_enabeler_1 :
      forall x, i : real.
      forall mode : fpa_rounding_mode.
      forall exp_min, prec : int
      [
         float(prec, exp_min, mode, x),
         is_theory_constant(prec),
         is_theory_constant(exp_min),
         is_theory_constant(mode),
         float(prec, exp_min, mode, x) in [?, i]
      ]
      { float(prec, exp_min, mode, x) <= i }.
      float(prec, exp_min, mode, x) = i or float(prec, exp_min, mode, x) < i

   axiom contrapositive_enabeler_2 :
      forall x, i : real.
      forall mode : fpa_rounding_mode.
      forall exp_min, prec : int
      [
         float(prec, exp_min, mode, x),
         is_theory_constant(prec),
         is_theory_constant(exp_min),
         is_theory_constant(mode),
         float(prec, exp_min, mode, x) in [i, ?]
      ]
      { float(prec, exp_min, mode, x) >= i }.
      float(prec, exp_min, mode, x) = i or float(prec, exp_min, mode, x) > i


   axiom gradual_underflow_1:
      forall x, y : real. (* semantic triggers are missing! can we do better ? i.e. >= cst *)
      forall mode : fpa_rounding_mode.
      forall exp_min, prec : int
      [
         float(prec, exp_min, mode, float(prec, exp_min, mode, x) - float(prec, exp_min, mode, y)),
         is_theory_constant(prec),
         is_theory_constant(exp_min),
         is_theory_constant(mode)
      ].
      float(prec, exp_min, mode, x) > float(prec, exp_min, mode, y) ->
      float(prec, exp_min, mode, float(prec, exp_min, mode, x) - float(prec, exp_min, mode, y)) > 0.

   axiom gradual_underflow_2:
      forall x, y : real. (* semantic triggers are missing! can we do better ? i.e. >= cst *)
      forall mode : fpa_rounding_mode.
      forall exp_min, prec : int
      [
         float(prec, exp_min, mode, float(prec, exp_min, mode, x) + float(prec, exp_min, mode, y)),
         is_theory_constant(prec),
         is_theory_constant(exp_min),
         is_theory_constant(mode)
      ].
      float(prec, exp_min, mode, x) > - float(prec, exp_min, mode, y) ->
      float(prec, exp_min, mode, float(prec, exp_min, mode, x) + float(prec, exp_min, mode, y)) > 0.


   axiom gradual_underflow_3:
      forall x, y : real. (* semantic triggers are missing! can we do better ? i.e. >= cst *)
      forall mode : fpa_rounding_mode.
      forall exp_min, prec : int
      [
         float(prec, exp_min, mode, float(prec, exp_min, mode, x) - float(prec, exp_min, mode, y)),
         is_theory_constant(prec),
         is_theory_constant(exp_min),
         is_theory_constant(mode)
      ].
      float(prec, exp_min, mode, x) < float(prec, exp_min, mode, y) ->
      float(prec, exp_min, mode, float(prec, exp_min, mode, x) - float(prec, exp_min, mode, y)) < 0.

   axiom gradual_underflow_4:
      forall x, y : real. (* semantic triggers are missing! can we do better ? i.e. >= cst *)
      forall mode : fpa_rounding_mode.
      forall exp_min, prec : int
      [
         float(prec, exp_min, mode, float(prec, exp_min, mode, x) + float(prec, exp_min, mode, y)),
         is_theory_constant(prec),
         is_theory_constant(exp_min),
         is_theory_constant(mode)
      ].
      float(prec, exp_min, mode, x) < - float(prec, exp_min, mode, y) ->
      float(prec, exp_min, mode, float(prec, exp_min, mode, x) + float(prec, exp_min, mode, y)) < 0.


   axiom float_of_float_same_formats:
      forall x : real.
      forall mode1, mode2 : fpa_rounding_mode.
      forall exp_min, prec : int
      [
         float(prec, exp_min, mode1, float(prec, exp_min, mode2, x)),
         is_theory_constant(prec),
         is_theory_constant(exp_min),
         is_theory_constant(mode1),
         is_theory_constant(mode2)
      ].
      float(prec, exp_min, mode1, float(prec, exp_min, mode2, x)) =
      float(prec, exp_min, mode2, x)

   axiom float_of_float_different_formats:
      forall x : real.
      forall mode1, mode2 : fpa_rounding_mode.
      forall exp_min1, prec1, exp_min2, prec2 : int
      [
         float(prec1, exp_min1, mode1, float(prec2, exp_min2, mode2, x)),
         is_theory_constant(prec1),
         is_theory_constant(exp_min1),
         is_theory_constant(prec2),
         is_theory_constant(exp_min2),
         is_theory_constant(mode1),
         is_theory_constant(mode2)
      ].
      prec2 <= prec1 ->
      exp_min2 <= exp_min1 ->
      float(prec1, exp_min1, mode1, float(prec2, exp_min2, mode2, x)) =
      float(prec2, exp_min2, mode2, x)


   axiom tighten_float_intervals_1__min_large : (* add a semantic trigger on o(i) - i *)
     forall x : real.
     forall i, k : real.
     forall mode : fpa_rounding_mode.
     forall p, m : int
     [
        float(m, p, mode, x),
        is_theory_constant(m),
        is_theory_constant(p),
        is_theory_constant(mode),
        float(m, p, mode, x) in [i, ?],
        k |-> float(m, p, Up, i)
     ]
     {
        i <= float(m, p, mode, x)
     }.
     (*i < k -> not needed => subsumed *)
     k <= float(m, p, mode, x)

   axiom tighten_float_intervals__2__min_strict : (* add a semantic trigger on o(i) - i *)
     forall x : real.
     forall i, k : real.
     forall mode : fpa_rounding_mode.
     forall p, m : int
     [
        float(m, p, mode, x),
        is_theory_constant(m),
        is_theory_constant(p),
        is_theory_constant(mode),
        float(m, p, mode, x) in ]i, ?],
        k |-> float(m, p, Up, i)
     ]
     {
        i < float(m, p, mode, x)
     }. (* we can improve even if this condition is not true, with epsilon *)
     (*i < k -> not needed => subsumed*)
     k <= float(m, p, mode, x)

   axiom tighten_float_intervals_3__max_large : (* add a semantic trigger on o(i) - i *)
     forall x : real.
     forall i, k : real.
     forall mode : fpa_rounding_mode.
     forall p, m : int
     [
        float(m, p, mode, x),
        is_theory_constant(m),
        is_theory_constant(p),
        is_theory_constant(mode),
        float(m, p, mode, x) in [?, i],
        k |-> float(m, p, Down, i)
     ]
     {
        i >= float(m, p, mode, x)
     }.
     (*k < i -> not needed => subsumed*)
     k >= float(m, p, mode, x)

   axiom tighten_float_intervals__4__max_strict : (* add a semantic trigger on o(i) - i *)
     forall x : real.
     forall i, k : real.
     forall mode : fpa_rounding_mode.
     forall p, m : int
     [
        float(m, p, mode, x),
        is_theory_constant(m),
        is_theory_constant(p),
        is_theory_constant(mode),
        float(m, p, mode, x) in [?, i[,
        k |-> float(m, p, Down, i)
     ]
     {
        float(m, p, mode, x) < i
     }. (* we can improve even if this condition is not true, with epsilon *)
     (*k < i -> not needed => subsumed*)
     float(m, p, mode, x) <= k


   axiom float_of_minus_float:
     forall x : real.
     forall mode : fpa_rounding_mode.
     forall p, m : int
     [
        float(m, p, mode, - float(m, p, mode, x)),
        is_theory_constant(m),
        is_theory_constant(p),
        is_theory_constant(mode)
     ].
     float(m, p, mode, - float(m, p, mode, x)) = - float(m, p, mode, float(m, p, mode, x))
     (* which can be directly simplified to - float(m, p, mode, x). Another axiom will do this *)
     (* this axiom probably applies more generally to float(m, p, mode, - x) = - float(m, p, mode, x) *)


   axiom float_of_int:
     forall x : int.
     forall k : real.
     forall mode : fpa_rounding_mode.
     forall exp_min, prec : int
     [
        float(prec, exp_min, mode, real_of_int(x)),
        is_theory_constant(prec),
        is_theory_constant(exp_min),
        is_theory_constant(mode),
        real_of_int(x) + (2 **. prec)  in [0., ?],
        real_of_int(x) - (2 **. prec) in [?, 0.],
        k |-> 2 **. prec
     ]
     {
        -k <= real_of_int(x),
        real_of_int(x) <= k
     }.
     float(prec, exp_min, mode, real_of_int(x)) = real_of_int(x)


   axiom float_of_pos_pow_of_two:
     forall x, y, i, k1, k2 : real.
     forall mode : fpa_rounding_mode.
     forall p, m : int
     [
        float(m, p, mode, x * float(m, p, mode, y)),
        is_theory_constant(p),
        is_theory_constant(m),
        is_theory_constant(mode),
        is_theory_constant(x),
        x in [i , i],
        k1 |-> abs_real(i),
        k2 |-> 2 **. (integer_log2(abs_real(i)))
     ].
     k1 >= 1. ->
     k1 = k2 -> (* is pow of 2 ?*)
     float(m, p, mode, x * float(m, p, mode, y)) = x * float(m, p, mode, y)


   axiom tighten_open_float_bounds :
     forall x : real.
     forall i, j, i2, j2 : real.
     forall mode : fpa_rounding_mode.
     forall p, m : int
     [
        float(m, p, mode, x),
        is_theory_constant(m),
        is_theory_constant(p),
        is_theory_constant(mode),
        float(m, p, mode, x) in ]i, j[,
        i2 |-> float(m, p, Up, i + (2 **. (2 * (- p)))),
        j2 |-> float(m, p, Down, j - (2 **. (2 * (- p))))
        (* pow_real_int(2.,2 * (- p)) is smaller than any gap between two successive floats *)
     ]
     {
        float(m, p, mode, x) > i,
        float(m, p, mode, x) < j
     }.
     i = float(m, p, mode, i) ->
     j = float(m, p, mode, j) ->
     i2 <= float(m, p, mode, x) <= j2

end
              |}

let ria_ae =
{|

(*** Handling of real_of_int and real_is_int: ***)
theory Real_of_Int extends RIA =
   axiom rii : forall x : real [real_is_int(x)]. real_is_int(x) = (x = real_of_int(int_floor(x)))

   axiom roi_add :
     forall x, y : int [real_of_int(x+y)].
       real_of_int(x + y) = real_of_int(x) + real_of_int(y)

   axiom roi_sub :
     forall x, y : int [real_of_int(x-y)].
       real_of_int(x - y) = real_of_int(x) - real_of_int(y)

   axiom roi_mult :
     forall x, y : int [real_of_int(x*y)].
       real_of_int(x * y) = real_of_int(x) * real_of_int(y)

   axiom roi_monotonicity_1 :
     forall x : int.
     forall k : real.
     forall i : int
     [real_of_int(x), x in ]?, i], k |-> real_of_int(i)]
     {x <= i}.
     real_of_int(x) <= k

   axiom roi_monotonicity_2 :
     forall x : int.
     forall k : real.
     forall i : int
     [real_of_int(x), x in [i, ?[, k |-> real_of_int(i)]
     {i <= x}.
     k <= real_of_int(x)

   axiom real_of_int_to_int_1 :
     forall x, k : int.
     forall i : real
     [real_of_int(x), real_of_int(x) in ]?, i], k |-> int_floor(i)]
     {real_of_int(x) <= i}.
     x <= k

   axiom real_of_int_to_int_2 :
     forall x, k : int.
     forall i : real
     [real_of_int(x), real_of_int(x) in [i, ?[, k |-> int_ceil(i)]
     {i <= real_of_int(x)}.
     k <= x

  (* floor(x) ≤ i iff x < i + 1 *)
  axiom int_floor_ub:
    forall x, y : real, i : int
    [ int_floor(x), not_theory_constant(x), int_floor(x) in ]?, i], y |-> real_of_int(i + 1) ]
    { int_floor(x) <= i }.
    x < y

  (* i <= floor(x) iff i <= x *)
  axiom int_floor_lb:
    forall x, y : real, i : int
    [ int_floor(x), not_theory_constant(x), int_floor(x) in [i, ?[, y |-> real_of_int(i) ]
    { i <= int_floor(x) }.
    y <= x

  (* ceil(x) ≤ i iff x ≤ i *)
  axiom int_ceil_ub:
    forall x, y : real, i : int
    [ int_ceil(x), not_theory_constant(x), int_ceil(x) in ]?, i], y |-> real_of_int(i) ]
    { int_ceil(x) <= i }.
    x <= y

  (* i <= ceil(x) iff i - 1 < x *)
  axiom int_ceil_lb:
    forall x, y : real, i : int
    [ int_ceil(x), not_theory_constant(x), int_ceil(x) in [i, ?[, y |-> real_of_int(i - 1) ]
    { i <= int_ceil(x) }.
    y < x

   (* can add other axioms on strict ineqs on rationals ? *)

end

theory ABS extends RIA =

   axiom abs_real_pos :
     forall x : real
     [
        abs_real(x),
        x in [0., ?[
     ]
     {x >= 0.}.
     abs_real(x) = x

  axiom abs_real_neg :
     forall x : real
     [
        abs_real(x),
        x in ]?, 0.]
     ]
     {x <= 0.}.
     abs_real(x) = -x

   case_split abs_real_cs:
     forall x : real
     [
        abs_real(x),
        x in [?i,?j],
        0. in ]?i,?j[
     ].
     (* not of the form (a or not a) to avoid simplification of F.mk_or *)
     x <= 0. or x >= 0.

   axiom abs_real_interval_1 :
     forall x : real
     [
        abs_real(x),
        abs_real(x) in [?i, ?j],
        0. in ]?i, ?j[
     ].
     0. <= abs_real(x)

   axiom abs_real_interval_2 : (* should block this axiom once the deduction is made,
         but this needs to have i and j on the left-hand-side of semantic triggers *)
     forall i, j, k : real.
     forall x : real
     [
        abs_real(x),
        x in [i, j],
        k |-> max_real (abs_real(i), abs_real(j))
     ]
     {i <= x, x <= j}.
     abs_real(x) <= k

   axiom abs_real_interval_3 : (* should block this axiom once the deduction is made,
         but this needs to have i and j on the left-hand-side of semantic triggers *)
     forall i : real.
     forall x : real
     [
        abs_real(x),
        abs_real(x) in [?, i]
     ]
     { abs_real(x) <= i }.
     - i <= x <= i

   axiom abs_real_from_square_large:
     forall x, y : real[x*x,y*y]. (* semantic triggers mising *)
       x*x <= y*y ->
       abs_real(x) <= abs_real(y)

   axiom abs_real_from_square_strict:
     forall x, y : real[x*x,y*y]. (* semantic triggers mising *)
       x*x < y*y ->
       abs_real(x) < abs_real(y)


   axiom abs_real_greater_than_real :
     forall x : real
     [
        abs_real(x)
     ].
     x <= abs_real(x)


  (* TODO: add semantic triggers not_theory_constant(x) on axioms of abs_int *)

   axiom abs_int_pos :
     forall x : int[abs_int(x) , x in [0, ?[ ]
     {x >= 0}.
     abs_int(x) = x

  axiom abs_int_neg :
     forall x : int[abs_int(x), x in ]?, 0]]
     {x <= 0}.
     abs_int(x) = -x

   case_split abs_int_cs:
     forall x : int [abs_int(x) , x in [?i,?j], 0 in ]?i,?j[].
     (* not of the form (a or not a) to avoid simplification of F.mk_or *)
     x <= 0 or x >= 0

  axiom abs_int_interval_1 :
     forall x : int [abs_int(x), abs_int(x) in [?i, ?j], 0 in ]?i, ?j[].
     0 <= abs_int(x)

  axiom abs_int_interval_2 :
     forall i, j, k : int.
     forall x : int [abs_int(x), x in [i, j], k |-> max_int (abs_int(i), abs_int(j))]
     {i <= x , x <= j}.
     abs_int(x) <= k

  axiom abs_int_interval_3 :
     forall i : int.
     forall x : int [abs_int(x), abs_int(x) in [?, i]]
     { abs_int(x) <= i }.
     - i <= x <= i

end
 |}

let nra_ae = {|
theory Principal_Sqrt_real extends NRA = (* some axioms about sqrt: shoud add more *)

axiom sqrt_bounds:
      forall x, i, j : real
      [sqrt_real(x), x in [i,j]]
      (* x may be a constant. i.e. x = i = j and sqrt_real(x) is not exact *)
      {i <= x, x <= j}.
      sqrt_real_default(i) <= sqrt_real(x) <= sqrt_real_excess(j)

axiom sqrt_real_is_positive:
  forall x:real[sqrt_real(x)]. (* semantic triggers ? case-split ? *)
     x >= 0. ->
     sqrt_real(x) >= 0.

axiom sqrt_real_is_positive_strict:
  forall x:real[sqrt_real(x)]. (* semantic triggers ? case-split ? *)
     x > 0. ->
     sqrt_real(x) > 0.

axiom square_of_sqrt_real:
  forall x:real[sqrt_real(x)]. (* semantic triggers ? case-split ? *)
    x >= 0. ->
    sqrt_real(x) * sqrt_real(x) = x

axiom sqrt_real_of_square:
  forall x:real[sqrt_real(x * x)]. (* semantic triggers ? case-split ? *)
    x >= 0. ->
    sqrt_real(x * x) = x


axiom sqrt_real_monotonicity:
  forall x, y:real[sqrt_real(x), sqrt_real(y)].
    (* semantic triggers ? case-split ? *)
    x >= 0. ->
    y >= 0. ->
    x <= y ->
    sqrt_real(x) <= sqrt_real(y)

(* what about contrapositive of sqrt_real_monotonicity *)

axiom sqrt_real_monotonicity_strict:
  forall x, y:real[sqrt_real(x), sqrt_real(y)].
    (* semantic triggers ? case-split ? *)
    x >= 0. ->
    y >= 0. ->
    x < y ->
    sqrt_real(x) < sqrt_real(y)

(* what about contrapositive of sqrt_real_monotonicity_strict *)

end

theory Linearization extends NRA =

   (* TODO: linearizations with strict inequalities are missing *)

   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_mult_1:
         forall x, y: real.
         forall a: real
         [
            x*y,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [a,?]
          |
            y*x,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [a,?]
         ]
         {a <= y}.
         x >= 0. ->
         x*a <= x*y

   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_mult_2:
         forall x, y: real.
         forall a: real
         [
            x*y,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [a,?]
          |
            y*x,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [a,?]
         ]
         {a <= y}.
         x <= 0. ->
         x*a >= x*y

  (* needs more semantic triggers, case-split, and discarding of linear terms*)
  axiom linearize_mult_3:
         forall x, y: real.
         forall b: real
         [
            x*y,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [?,b]
          |
            y*x,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [?,b]
         ]
         {y <= b}.
         x >= 0. ->
         x*y <= x*b

   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_mult_4:
         forall x, y: real.
         forall b: real
         [
            x*y,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [?,b]
          |
            x*y,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [?,b]
         ]
         {y <= b}.
         x <= 0. ->
         x*y >= x*b


   (* commutativity of four axiomes above *)
   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_mult_5:
         forall x, y: real.
         forall a: real
         [
            y*x,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [a,?]
          |
            x*y,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [a,?]
         ]
         {a <= y}.
         x >= 0. ->
         a*x <= y*x

   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_mult_6:
         forall x, y: real.
         forall a: real
         [
            y*x,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [a,?]
          |
            x*y,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [a,?]
         ]
         {a <= y}.
         x <= 0. ->
         a*x >= y*x

  (* needs more semantic triggers, case-split, and discarding of linear terms*)
  axiom linearize_mult_7:
         forall x, y: real.
         forall b: real
         [
            y*x,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [?,b]
          |
            x*y,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [?,b]
         ]
         {y <= b}.
         x >= 0. ->
         y*x <= b*x

   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_mult_8:
         forall x, y: real.
         forall b: real
         [
            y*x,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [?,b]
          |
            x*y,
            not_theory_constant(x),
            not_theory_constant(y),
            y in [?,b]
         ]
         {y <= b}.
         x <= 0. ->
         y*x >= b*x


   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_div_1:
    forall a, b, c : real
    [
       a/b,
       not_theory_constant(b),
       a/b in [c, ?]
    ]
    {a/b >= c}.
    b > 0. ->
    a >= b * c

   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_div_2:
    forall a, b, c : real
    [
       a/b,
       not_theory_constant(b),
       a/b in [c, ?]
    ]
    {a/b >= c}.
    b < 0. ->
    a <= b * c

   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_div_3:
    forall a, b, c : real
    [
       a/b,
       not_theory_constant(b),
       a/b in [?, c]
    ]
    {a/b <= c}.
    b > 0. ->
    a <= b * c

   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_div_4:
    forall a, b, c : real
    [
       a/b,
       not_theory_constant(b),
       a/b in [?, c]
    ]
    {a/b <= c}.
    b < 0. ->
    a >= b * c


   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_div_strict_1:
    forall a, b, c : real
    [
       a/b,
       not_theory_constant(b),
       a/b in ]c, ?]
    ]
    {a/b > c}.
    b > 0. ->
    a > b * c

   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_div_strict_2:
    forall a, b, c : real
    [
       a/b,
       not_theory_constant(b),
       a/b in ]c, ?]
    ]
    {a/b > c}.
    b < 0. ->
    a < b * c

   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_div_strict_3:
    forall a, b, c : real
    [
       a/b,
       not_theory_constant(b),
       a/b in [?, c[
    ]
    {a/b < c}.
    b > 0. ->
    a < b * c

   (* needs more semantic triggers, case-split, and discarding of linear terms*)
   axiom linearize_div_strict_4: (* add the same thing for equality ?? *)
    forall a, b, c : real
    [
       a/b,
       not_theory_constant(b),
       a/b in [?, c[
    ]
    {a/b < c}.
    b < 0. ->
    a > b * c


   axiom linearize_mult_zero_one_1:
     forall x, y : real
     [
        x*y,
        not_theory_constant(x),
        not_theory_constant(y),
        x in [0., 1.]
     ]
     {0. <= x, x <= 1.}. (* needs cs on y an sem trigger on y *)
     y >= 0. ->
     x*y <= y

   axiom linearize_mult_zero_one_2:
     forall x, y : real
     [
        y*x,
        not_theory_constant(x),
        not_theory_constant(y),
        x in [0., 1.]
     ]{0. <= x, x <= 1.}. (* needs cs on y an sem trigger on y *)
     y >= 0. ->
     y*x <= y

   axiom linearize_mult_zero_one_3:
     forall x, y : real
     [
        x*y,
        not_theory_constant(x),
        not_theory_constant(y),
        x in [0., 1.]
     ]{0. <= x, x <= 1.}. (* needs cs on y an sem trigger on y *)
     y <= 0. ->
     y <= x*y

   axiom linearize_mult_zero_one_4:
     forall x, y : real
     [
        y*x,
        not_theory_constant(x),
        not_theory_constant(y),
        x in [0., 1.]
     ]{0. <= x, x <= 1.}. (* needs cs on y an sem trigger on y *)
     y <= 0. ->
     y <= y*x

   axiom linearize_mult_zero_one_5:
     forall x, y : real
     [
        x*y,
        not_theory_constant(x),
        not_theory_constant(y),
        -x in [0., 1.]
     ]{-1. <= x, x <= 0.}. (* needs cs on y an sem trigger on y *)
     y >= 0. ->
     x*y <= y

   axiom linearize_mult_zero_one_6:
     forall x, y : real
     [
        y*x,
        not_theory_constant(x),
        not_theory_constant(y),
        -x in [0., 1.]
     ]{-1. <= x, x <= 0.}. (* needs cs on y an sem trigger on y *)
     y >= 0. ->
     y*x <= y

   axiom linearize_mult_zero_one_7:
     forall x, y : real
     [
        x*y,
        not_theory_constant(x),
        not_theory_constant(y),
        -x in [0., 1.]
     ]{-1. <= x, x <= 0.}. (* needs cs on y an sem trigger on y *)
     y <= 0. ->
     y <= x*y

   axiom linearize_mult_zero_one_8:
     forall x, y : real
     [
        y*x,
        not_theory_constant(x),
        not_theory_constant(y),
        -x in [0., 1.]
     ]{-1. <= x, x <= 0.}. (* needs cs on y an sem trigger on y *)
     y <= 0. ->
     y <= y*x

end
|}

let pp_prelude ppf = function
  | Fpa -> Format.fprintf ppf "fpa"
  | Ria -> Format.fprintf ppf "ria"
  | Nra -> Format.fprintf ppf "nra"

type t =
  | Prelude of prelude
  | ADT
  | AC

let pp ppf = function
  | Prelude p -> pp_prelude ppf p
  | ADT -> Format.fprintf ppf "adt"
  | AC -> Format.fprintf ppf "ac"

let filename =
  Format.asprintf "<builtins>/%a.ae" pp_prelude

let content = function
  | Fpa -> fpa_ae
  | Ria -> ria_ae
  | Nra -> nra_ae

let all_preludes = [ Fpa; Ria; Nra ]

let all = ADT :: AC :: List.map (fun p -> Prelude p) all_preludes

(* By default we disable Fpa, Ria and Nra preludes to prevent
   regressions. *)
let default_preludes = []

let default = [ ADT; AC ]

let preludes =
  List.filter_map (function | Prelude p -> Some p | _ -> None)
