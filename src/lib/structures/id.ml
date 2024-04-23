(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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

type t = {
  name : Hstring.t;
  tag : int;
}

let equal { tag = t1; _ } { tag = t2; _ } = t1 = t2

let compare { tag = t1; _ } { tag = t2; _ } = t1 - t2

let hash { tag; _ } = tag

type typed = t * Ty.t list * Ty.t [@@deriving ord]

let pp ?(full = false) ppf { name; tag } =
  let name = Hstring.view name in
  if full then
    Fmt.pf ppf "%a%d"
      Dolmen.Smtlib2.Script.Poly.Print.id (Dolmen.Std.Name.simple name)
      tag
  else
    Dolmen.Smtlib2.Script.Poly.Print.id ppf (Dolmen.Std.Name.simple name)

let show ?(full = false) = Fmt.to_to_string (pp ~full)

let cpt : int ref = ref 0

let reinit () =
  cpt := 0

let make name =
  let res = { name = Hstring.make name; tag = !cpt } in
  incr cpt;
  res

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
