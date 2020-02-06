open Options
open Format

type incr_kind = Matching | Omega | Fourier | Uf | Builtin | Ac | Naive of int

let naive_steps = ref 0
let steps = ref 0
let mult_f = ref 0
let mult_m = ref 0
let mult_s = ref 0
let mult_uf = ref 0
let mult_b = ref 0
let mult_a = ref 0

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

let get_steps () =
  max !naive_steps !steps