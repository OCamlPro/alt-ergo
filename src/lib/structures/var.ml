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
type t =
  | Underscore
  | Local of Id.t
  | Named of Id.t

let[@inline always] local id =
  assert (
    let s = Id.show id in
    Compat.String.starts_with ~prefix:"?" s);
  Local id

let[@inline always] of_id i =
  assert (
    match i with
    | Id.Term_cst _ | Hstring { ns = Skolem; _ } -> true
    | _ -> false);
  Named i

(* Note: there is a single [Underscore] variable, with id 0. *)
let underscore = Underscore

let is_local v = match v with Local _ -> true | _ -> false

let uid v =
  match v with
  | Underscore -> 0
  | Local i -> 3 * Id.hash i + 1
  | Named i -> 3 * Id.hash i + 2

let hash = uid

let equal_repr v1 v2 =
  match v1, v2 with
  | Underscore, Underscore -> true
  | Underscore, _ | _, Underscore -> false
  | Local i1, Local i2
  | Named i1, Named i2 -> Id.equal i1 i2
  | Local _, Named _ | Named _, Local _ -> false

let compare a b =
  let c = (uid a) - (uid b) in
  if c <> 0 then c
  else begin
    assert (equal_repr a b);
    c
  end

let equal a b = compare a b = 0

let pp ppf = function
  | Underscore -> Fmt.pf ppf "_"
  | Local i | Named i ->
    Fmt.pf ppf "%a~%d" Id.pp i (Id.hash i)

let show = Fmt.to_to_string pp

module Set = Set.Make(struct type nonrec t = t let compare = compare end)

module Map = struct
  include Map.Make (struct type nonrec t = t let compare = compare end)

  let pp pp_elt =
    let sep ppf () = Fmt.pf ppf " -> " in
    Fmt.box @@ Fmt.braces
    @@ Fmt.iter_bindings ~sep:Fmt.comma iter
    @@ Fmt.pair ~sep pp pp_elt
end
