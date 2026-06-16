(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2022-2024 --- OCamlPro SAS                           *)
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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(* Note: keep the constructors in the same order as in the definition in
   [prelude_to_int] so that it gets simplified to the identity. *)
type prelude = Nra | Ria | Fpa

let[@inline] prelude_to_int = function
  | Nra -> 0
  | Ria -> 1
  | Fpa -> 2

let pp_prelude ppf = function
  | Fpa -> Format.fprintf ppf "fpa"
  | Ria -> Format.fprintf ppf "ria"
  | Nra -> Format.fprintf ppf "nra"

let equal_prelude prelude1 prelude2 =
  Int.equal
    (prelude_to_int prelude1)
    (prelude_to_int prelude2)

let compare_prelude p1 p2 =
  Int.compare (prelude_to_int p1) (prelude_to_int p2)

type t =
  | Prelude of prelude
  | ADT
  | AC

let equal t1 t2 =
  match t1, t2 with
  | Prelude p1, Prelude p2 ->
    equal_prelude p1 p2
  | ADT, ADT
  | AC, AC ->
    true
  | (Prelude _ | ADT | AC), _ ->
    false

let compare t1 t2 =
  match t1, t2 with
  | Prelude p1, Prelude p2 -> compare_prelude p1 p2
  | Prelude _, _ -> -1
  | _, Prelude _ -> 1

  | ADT, ADT -> 0
  | ADT, _ -> -1
  | _, ADT -> 1

  | AC, AC -> 0

let pp ppf = function
  | Prelude p -> pp_prelude ppf p
  | ADT -> Format.fprintf ppf "adt"
  | AC -> Format.fprintf ppf "ac"

let filename =
  Format.asprintf "<builtins>/%a.ae" pp_prelude

let get_prelude name =
  match Preludes.read name with
  | Some content -> content
  | None -> failwith (Fmt.str "Missing internal prelude: %s" name)

let fpa_prelude = get_prelude "fpa.ae"
let ria_prelude = get_prelude "ria.ae"
let nra_prelude = get_prelude "nra.ae"

let content = function
  | Fpa -> fpa_prelude
  | Ria -> ria_prelude
  | Nra -> nra_prelude

let all_preludes = [ Fpa; Ria; Nra ]

let all = ADT :: AC :: List.map (fun p -> Prelude p) all_preludes

let default_preludes = all_preludes

let default = all

let preludes =
  List.filter_map (function | Prelude p -> Some p | _ -> None)

module Set = Set.Make(struct type nonrec t = t let compare = compare end)
