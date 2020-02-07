open Options
open Format

(** Define the type of increment *)
type incr_kind =
    Matching (* Matching step increment *)
  | Omega (* Step of Arith on Real and Int *)
  | Fourier (* FourierMotzkin step increment *)
  | Uf (* UF step increment *)
  | Builtin (* Inequalities increment *)
  | Ac (* AC step reasoning *)
  | Naive of int (* Naive cpt increment the counter for cpt term assumed in the
                  * theories environment *)

let naive_steps = ref 0
let steps = ref 0
let mult_f = ref 0
let mult_m = ref 0
let mult_s = ref 0
let mult_uf = ref 0
let mult_b = ref 0
let mult_a = ref 0

(** Multipliers are here to homogeneize the global step counter *)
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
    | Builtin -> mult_b := !mult_b + 1;
      if !mult_b = 5 then
        (steps := !steps + 1;
         mult_b := 0)
    | Fourier -> mult_f := !mult_f + 1;
      if !mult_f = 40 then
        (steps := !steps + 1;
         mult_f := 0);
    | Naive n ->
      (* Since n refers to the number of terms sent to the theories no
       * multiplier is needed here *)
      if n < 0 then
        begin
          Format.eprintf "steps can only be positive@.";
          exit 1
        end;
      naive_steps := !naive_steps + n;
  end;
  if steps_bound () <> -1
  && ((Stdlib.compare !steps ((steps_bound ())) > 0)
      || (Stdlib.compare !naive_steps ((steps_bound ())) > 0)) then
    begin
      printf "Steps limit reached: %d@."
        (if !naive_steps > 0 then !naive_steps
         else if !steps > 0 then !steps
         else steps_bound ());
      exit 1
    end


let reset_steps () =
  naive_steps := 0;
  steps := 0;
  mult_f := 0;
  mult_m := 0;
  mult_s := 0;
  mult_uf := 0;
  mult_b := 0;
  mult_a := 0

(** Return the max steps between naive and refine steps counting. Both counter
 ** are compute at execution. The first one count the number of terms sent to
 ** the thories environment, the second one count steps depending of the
 ** theories used *)
let get_steps () =
  max !naive_steps !steps
