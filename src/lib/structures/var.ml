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

type view = {
  hs : Hstring.t ;
  id : int ;
}

type t = view

let cpt = ref 0

let of_hstring hs =
  incr cpt;
  {hs ; id = !cpt}

let of_string s =
  incr cpt;
  {hs = Hstring.make s; id = !cpt}

let view v = v

let compare a b =
  let c = a.id - b.id in
  if c <> 0 then c
  else begin
    assert (Hstring.equal a.hs b.hs);
    c
  end

let equal a b = compare a b = 0

let hash { id; _ } = id

let to_string {hs ; id} =
  Format.sprintf "%s~%d" (Hstring.view hs) id

let print fmt v =
  Format.fprintf fmt "%s" (to_string v)

let save_cnt, reinit_cnt =
  let saved_cnt = ref 0 in
  let save_cnt () =
    saved_cnt := !cpt
  in
  let reinit_cnt () =
    cpt := !saved_cnt
  in
  save_cnt, reinit_cnt


module Set = Set.Make(struct type t = view let compare = compare end)
module Map = Map.Make(struct type t = view let compare = compare end)
