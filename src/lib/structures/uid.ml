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
  | Hstring of Hstring.t
  | Unique of { name : Hstring.t; index : int }

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

let[@inline always] of_dolmen DE.{ path; index; _ } =
  let name = Hstring.make @@ get_basename path in
  Unique { name; index = (index :> int) }

let[@inline always] of_hstring hs = Hstring hs
let[@inline always] of_string s = of_hstring @@ Hstring.make s

let hash = function
  | Hstring hs -> Hstring.hash hs
  | Unique { index; _ } -> index

let pp ppf = function
  | Hstring hs -> Hstring.print ppf hs
  | Unique { name; _ } -> Hstring.print ppf name

let show = Fmt.to_to_string pp

let equal u1 u2 =
  match u1, u2 with
  | Hstring hs1, Hstring hs2 -> Hstring.equal hs1 hs2
  | Unique { index = i1; _ }, Unique { index = i2; _ }-> i1 = i2
  | _ -> false

let compare u1 u2 =
  match u1, u2 with
  | Hstring hs1, Hstring hs2 -> Hstring.compare hs1 hs2
  | Unique { index = i1; _ }, Unique { index = i2; _ } -> i1 - i2
  | _ -> -1

let rec list_assoc x = function
  | [] -> raise Not_found
  | (y, v) :: l -> if equal x y then v else list_assoc x l

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
