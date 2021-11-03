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

type t = { content : string ; id : int}

module S =
  Hconsing.Make(struct
    type elt = t
    let hash s = Hashtbl.hash s.content
    let eq s1 s2 = String.equal s1.content s2.content
    let set_id n v = {v with id = n}
    let initial_size = 9001
    let disable_weaks () = Options.get_disable_weaks ()
  end)

let make s = S.make {content = s; id = - 1}

let view s = s.content

let print fmt v = Format.fprintf fmt "%s" (view v)

let equal s1 s2 = s1.id == s2.id

let compare s1 s2 = compare s1.id s2.id

let hash s = s.id

let empty = make ""

let rec list_assoc x = function
  | [] -> raise Not_found
  | (y, v) :: l -> if equal x y then v else list_assoc x l

let fresh_string, reset_fresh_string_cpt =
  let cpt = ref 0 in
  let fresh_string () =
    incr cpt;
    "!k" ^ (string_of_int !cpt)
  in
  let reset_fresh_string_cpt () =
    cpt := 0
  in
  fresh_string, reset_fresh_string_cpt

let is_fresh_string s =
  try s.[0] == '!' && s.[1] == 'k'
  with Invalid_argument s ->
    assert (String.compare s "index out of bounds" = 0);
    false

let is_fresh_skolem s =
  try s.[0] == '!' && s.[1] == '?'
  with Invalid_argument s ->
    assert (String.compare s "index out of bounds" = 0);
    false

let reinit () =
  (*
    "~n:25" because of the constants initialized in:
        hstring.ml:           empty
        ty.ml:                tunit
        symbols.ml:           underscore, fake_eq, fake_neq, fake_lt, fake_le
        fpa_rounding.ml:      fpa_rounding_mode (mode_constrs (x11), mode_ty),
                              _No__rounding_mode
        arith.ml:             mod_symb
        intervals.ml:         is_question_mark
        intervalCalculus.ml:  not_theory_const, is_theory_const, linear_dep
        ccx.ml, use.ml:       one

    The value is not reset to 26 because the next_id is incremented in
    the call to Hconsing.make in Shostak.Combine.empty.
  *)
  S.reinit ~n:25 ();
  reset_fresh_string_cpt ()

module Arg = struct type t'= t type t = t' let compare = compare end
module Set : Set.S with type elt = t = Set.Make(Arg)
module Map : Map.S with type key = t = Map.Make(Arg)
