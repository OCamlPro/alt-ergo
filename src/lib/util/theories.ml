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

type prelude = Nra | Ria | Fpa [@@deriving eq]

let pp_prelude ppf = function
  | Fpa -> Format.fprintf ppf "fpa"
  | Ria -> Format.fprintf ppf "ria"
  | Nra -> Format.fprintf ppf "nra"

let compare_prelude p1 p2 =
  match p1, p2 with
  | Nra, Nra -> 0
  | Nra, _ -> -1
  | _, Nra -> 1

  | Ria, Ria -> 0
  | Ria, _ -> -1
  | _, Ria -> 1

  | Fpa, Fpa -> 0

type t =
  | Prelude of prelude
  | ADT
  | AC
[@@deriving eq]

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

let content = function
  | Fpa -> [%blob "src/preludes/fpa.ae"]
  | Ria -> [%blob "src/preludes/ria.ae"]
  | Nra -> [%blob "src/preludes/nra.ae"]

let all_preludes = [ Fpa; Ria; Nra ]

let all = ADT :: AC :: List.map (fun p -> Prelude p) all_preludes

let default_preludes = all_preludes

let default = all

let preludes =
  List.filter_map (function | Prelude p -> Some p | _ -> None)

module Set = Set.Make(struct type nonrec t = t let compare = compare end)
