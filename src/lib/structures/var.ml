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

type repr = Underscore | Local of Hstring.t | Named of Hstring.t
(** A variable can be:

    - The special `Underscore` variable that is used to discard values in
      triggers (the {!underscore} constant in this module should be the only
      such variable)
    - A local variable, used for semantic triggers and bound to the enclosing
      theory lemma (all local variable names start with '?')
    - A regular variable, either from the problem input or specified by the
      user. Depending on the input format, regular variable may start with '?'
      (e.g. in SMT-LIB format, this is allowed).
*)

let equal_repr v1 v2 =
  match v1, v2 with
  | Underscore, Underscore -> true
  | Underscore, _ | _, Underscore -> false
  | Local hs1, Local hs2
  | Named hs1, Named hs2 -> Hstring.equal hs1 hs2
  | Local _, Named _ | Named _, Local _ -> false

let pp_repr ppf = function
  | Underscore -> Fmt.pf ppf "_"
  | Local hs | Named hs -> Hstring.print ppf hs

type t = { repr : repr ; id : int }

let fresh, save_cnt, reinit_cnt =
  let cpt = ref 0 in
  let fresh repr = incr cpt; { repr ; id = !cpt } in
  let saved_cnt = ref 0 in
  let save_cnt () =
    saved_cnt := !cpt
  in
  let reinit_cnt () =
    cpt := !saved_cnt
  in
  fresh, save_cnt, reinit_cnt

let of_hstring hs = fresh (Named hs)

let of_string s = of_hstring (Hstring.make s)

let local s =
  assert (String.length s > 0 && Char.equal '?' s.[0]);
  fresh (Local (Hstring.make s))

let is_local { repr; _ } = match repr with Local _ -> true | _ -> false

let compare a b =
  let c = a.id - b.id in
  if c <> 0 then c
  else begin
    assert (equal_repr a.repr b.repr);
    c
  end

let equal a b = compare a b = 0

let uid { id; _ } = id

let hash = uid

(* Note: there is a single [Underscore] variable, with id 1. *)
let underscore = fresh Underscore

let print ppf { repr; id } = Fmt.pf ppf "%a~%d" pp_repr repr id

let to_string = Fmt.to_to_string print

module Set = Set.Make(struct type nonrec t = t let compare = compare end)

module Map = struct
  include Map.Make (struct type nonrec t = t let compare = compare end)

  let pp pp_elt =
    let sep ppf () = Fmt.pf ppf " -> " in
    Fmt.box @@ Fmt.braces
    @@ Fmt.iter_bindings ~sep:Fmt.comma iter
    @@ Fmt.pair ~sep print pp_elt
end
