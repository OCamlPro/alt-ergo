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
type prelude =
  | Nra
  | Ria
  | Fpa
  | SmtFloat

let[@inline] prelude_to_int = function
  | Nra -> 0
  | Ria -> 1
  | Fpa -> 2
  | SmtFloat -> 3

let pp_prelude ppf = function
  | Fpa -> Format.fprintf ppf "fpa"
  | Ria -> Format.fprintf ppf "ria"
  | Nra -> Format.fprintf ppf "nra"
  | SmtFloat -> Format.fprintf ppf "smt.float"

let equal_prelude prelude1 prelude2 =
  Int.equal (prelude_to_int prelude1) (prelude_to_int prelude2)

let compare_prelude p1 p2 = Int.compare (prelude_to_int p1) (prelude_to_int p2)

type t =
  | Prelude of prelude
  | ADT
  | AC

let equal t1 t2 =
  match t1, t2 with
  | Prelude p1, Prelude p2 -> equal_prelude p1 p2
  | ADT, ADT | AC, AC -> true
  | (Prelude _ | ADT | AC), _ -> false

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

(** This type represents the status of a theory. It can be either:
    - [Default]: enabled by default
    - [Enabled]: explicitly(1) enabled
    - [Disabled]: explicitly(1) disabled

    (1) with a command-line option or [:set-option] *)
type status =
  | Default
  | Enabled
  | Disabled

let[@inline] status_to_int = function
  | Default -> 0
  | Enabled -> 1
  | Disabled -> 2

let equal_status status1 status2 =
  Int.equal (status_to_int status1) (status_to_int status2)

let pp_status ppf = function
  | Default -> Format.fprintf ppf "enabled by default"
  | Enabled -> Format.fprintf ppf "enabled"
  | Disabled -> Format.fprintf ppf "disabled"

let filename = Format.asprintf "<builtins>/%a.ae" pp_prelude

let get_prelude name =
  match Preludes.read name with
  | Some content -> content
  | None -> failwith (Fmt.str "Missing internal prelude: %s" name)

let fpa_prelude = get_prelude "fpa.ae"

let ria_prelude = get_prelude "ria.ae"

let nra_prelude = get_prelude "nra.ae"

let content = function
  | Fpa -> Some fpa_prelude
  | Ria -> Some ria_prelude
  | Nra -> Some nra_prelude
  | SmtFloat -> None

let all_preludes = [Fpa; Ria; Nra; SmtFloat]

(* SmtFloat is only activated when the user passes --enable-theories
   smt.float. *)
let default_preludes = [Fpa; Ria; Nra]

let all = ADT :: AC :: List.map (fun p -> Prelude p) all_preludes

let default = ADT :: AC :: List.map (fun p -> Prelude p) default_preludes

let theory_enum = List.map (fun t -> Format.asprintf "%a" pp t, t) all

let get_prelude = function Prelude p -> Some p | _ -> None

module Map = Map.Make (struct
  type nonrec t = t

  let compare = compare
end)

let upd_theory_status th ~enable m =
  Map.update th
    (fun current ->
      match current, enable with
      | Some Enabled, false | Some Disabled, true ->
        Fmt.failwith "theory '%a' cannot be both enabled and disabled" pp th
      | _, true -> Some Enabled
      | _ -> Some Disabled)
    m

let enable_theory m th = upd_theory_status th ~enable:true m

let disable_theory m th = upd_theory_status th ~enable:false m

let is_enabled th l =
  match List.assoc_opt th l with Some (Default | Enabled) -> true | _ -> false

let is_disabled th l =
  match List.assoc_opt th l with None | Some Disabled -> true | _ -> false
