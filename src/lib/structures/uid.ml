(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2024 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module DStd = Dolmen.Std
module DE = DStd.Expr

type t =
  | Hstring : Hstring.t -> t
  | Dolmen : 'a DE.id -> t

(** Helper function: returns the basename of a dolmen path, since in AE
    the problems are contained in one-file (for now at least), the path is
    irrelevant and only the basename matters *)
let get_basename = function
  | DStd.Path.Local { name; }
  | Absolute { name; path = []; } -> name
  | Absolute { name; path; } ->
    Fmt.failwith
      "Expected an empty path to the basename: \"%s\" but got: [%a]."
      name (fun fmt l ->
          match l with
          | h :: t ->
            Format.fprintf fmt "%s" h;
            List.iter (Format.fprintf fmt "; %s") t
          | _ -> ()
        ) path

let[@inline always] of_dolmen id = Dolmen id
let[@inline always] of_hstring hs = Hstring hs
let[@inline always] of_string s = of_hstring @@ Hstring.make s

let hash = function
  | Hstring hs -> Hstring.hash hs
  | Dolmen { index; _ } -> (index :> int)

let pp ppf = function
  | Hstring hs -> Hstring.print ppf hs
  | Dolmen { path; _ } -> Fmt.string ppf @@ get_basename path

let show = Fmt.to_to_string pp

let equal u1 u2 =
  match u1, u2 with
  | Hstring hs1, Hstring hs2 -> Hstring.equal hs1 hs2
  | Dolmen id1, Dolmen id2 -> DE.Id.equal id1 id2
  | _ ->
    Hstring.equal (Hstring.make @@ show u1) (Hstring.make @@ show u2)

let compare u1 u2 =
  match u1, u2 with
  | Hstring hs1, Hstring hs2 -> Hstring.compare hs1 hs2
  | Dolmen id1, Dolmen id2 -> DE.Id.compare id1 id2
  | _ -> Hstring.compare (Hstring.make @@ show u1) (Hstring.make @@ show u2)

module Set = Set.Make
    (struct
      type nonrec t = t
      let compare = compare
    end)

module Map = Map.Make
    (struct
      type nonrec t = t
      let compare = compare
    end)
