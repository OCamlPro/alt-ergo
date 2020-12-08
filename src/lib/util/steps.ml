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

open Options
open Errors

(* Define the type of increment *)
type incr_kind =
    Matching           (* Matching step increment *)
  | Interval_Calculus  (* Arith : Interval Calculus increment *)
  | Fourier            (* Arith : FourierMotzkin step increment *)
  | Omega              (* Arith : number of omega procedure on  Real and Int *)
  | Uf                 (* UF step increment *)
  | Ac                 (* AC step reasoning *)
  | Th_assumed of int  (* Increment the counter for each term assumed in the
                          theories environment *)

let naive_steps = ref 0
let steps = ref 0
let mult_f = ref 0
let mult_m = ref 0
let mult_s = ref 0
let mult_uf = ref 0
let mult_b = ref 0
let mult_a = ref 0

let all_steps = Stack.create ()

let push_steps () =
  Stack.push
    (!naive_steps,!steps,!mult_f,!mult_m,
     !mult_s,!mult_uf,!mult_b,!mult_a)
    all_steps

let pop_steps () =
  let p_naive_steps,p_steps, p_mult_f, p_mult_m,
      p_mult_s, p_mult_uf, p_mult_b, p_mult_a =
    Stack.pop all_steps in
  naive_steps := p_naive_steps;
  steps := p_steps;
  mult_f := p_mult_f;
  mult_m := p_mult_m;
  mult_s := p_mult_s;
  mult_uf := p_mult_uf;
  mult_b := p_mult_b;
  mult_a := p_mult_a

(* Multipliers are here to homogeneize the global step counter *)
let incr k =
  begin
    match k with
    | Uf -> mult_uf := !mult_uf + 1;
      if !mult_uf = 500 then
        (steps := !steps + 1;
         mult_uf := 0)
    | Matching -> mult_m := !mult_m + 1;
      if !mult_m = 100 then
        (steps := !steps + 1;
         mult_m := 0)
    | Omega -> mult_s := !mult_s + 1;
      if !mult_s = 2 then
        (steps := !steps + 1;
         mult_s := 0)
    | Ac -> mult_a := !mult_a + 1;
      if !mult_a = 1 then
        (steps := !steps + 1;
         mult_a := 0)
    | Interval_Calculus -> mult_b := !mult_b + 1;
      if !mult_b = 5 then
        (steps := !steps + 1;
         mult_b := 0)
    | Fourier -> mult_f := !mult_f + 1;
      if !mult_f = 40 then
        (steps := !steps + 1;
         mult_f := 0);
    | Th_assumed n ->
      (* Since n refers to the number of terms sent to the theories no
       * multiplier is needed here *)
      if n < 0 then
        run_error (Invalid_steps_count n);
      naive_steps := !naive_steps + n;
  end;
  let steps_bound = get_steps_bound () in
  if steps_bound <> -1
  && ((Stdlib.compare !steps ((steps_bound)) > 0)
      || (Stdlib.compare !naive_steps ((steps_bound)) > 0)) then
    begin
      let n =
        if !naive_steps > 0 then !naive_steps
        else if !steps > 0 then !steps
        else steps_bound
      in
      run_error (Steps_limit n)
    end


let reset_steps () =
  Stack.clear all_steps;
  naive_steps := 0;
  steps := 0;
  mult_f := 0;
  mult_m := 0;
  mult_s := 0;
  mult_uf := 0;
  mult_b := 0;
  mult_a := 0

(* Return the max steps between naive and refine steps counting. Both counter
 * are compute at execution. The first one count the number of terms sent to the
 * theories environment, the second one count steps depending of the theories
 * used *)
let get_steps () =
  max !naive_steps !steps


(** Functions useful for case-split steps *)
let cs_steps_cpt = ref 0
let cs_steps () = !cs_steps_cpt
let incr_cs_steps () = Stdlib.incr cs_steps_cpt
