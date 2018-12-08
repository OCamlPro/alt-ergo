(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Options
open Format

type t = {
  hs : Hstring.t ;
  id : int ;

  (* None -> not a let var. Some l -> list of direct and indirect
     quantified vars dependencies of this let var. *)
  let_deps : (t * Ty.t) list option ref;
}

type var = t

let compare a b =
  let c = a.id - b.id in
  if c <> 0 then c
  else begin
    assert (Hstring.equal a.hs b.hs);
    c
  end

let equal a b = compare a b = 0

let hash {hs ; id} = id

module Set = Set.Make(struct type t = var let compare = compare end)
module Map = Map.Make(struct type t = var let compare = compare end)

let cpt = ref 0

let of_hstring hs =
  incr cpt;
  {hs ; id = !cpt; let_deps = ref None}

let of_string s =
  incr cpt;
  {hs = Hstring.make s; id = !cpt; let_deps = ref None}

let set_let_deps v m = v.let_deps := Some (Map.bindings m)

let let_deps v = !(v.let_deps)

let hstring_part v = v.hs

let to_string {hs ; id} =
  sprintf "%s~%d" (Hstring.view hs) id

let print fmt v =
  fprintf fmt "%s" (to_string v)
