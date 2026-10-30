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

(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

include Container_types_intf

module Make_set (T : Thing) = struct
  include Set.Make [@inlined hint] (T)

  let print ppf set =
    Fmt.pf ppf "@[<1>{@[%a@]}@]" (Fmt.iter ~sep:Fmt.comma iter T.print) set

  exception More_than_one_element

  let get_singleton_exn set =
    (* O(1) non-allocating version from OxCaml. *)
    if is_empty set
    then raise Not_found
    else
      match
        fold
          (fun _elt count ->
            if count > 0 then raise_notrace More_than_one_element else 1)
          set 0
      with
      | (_ : int) -> choose set
      | exception More_than_one_element -> raise Not_found

  let get_singleton set =
    match get_singleton_exn set with
    | exception Not_found -> None
    | elt -> Some elt
end
[@@inline]

module Make_map (T : Thing) (Set : Set_plus_stdlib with type elt = T.t) = struct
  include Map.Make [@inlined hint] (T)
  module Set = Set

  let print print_datum ppf map =
    Fmt.pf ppf "@[<1>{@[%a@]}@]"
      (Fmt.iter_bindings ~sep:Fmt.comma iter
         (Fmt.pair ~sep:(Fmt.any " ->@ ") T.print print_datum
         |> Fmt.box ~indent:1))
      map

  exception More_than_one_binding

  let get_singleton_exn map =
    (* O(1) non-allocating version from OxCaml. *)
    if is_empty map
    then raise Not_found
    else
      match
        fold
          (fun _key _datum count ->
            if count > 0 then raise_notrace More_than_one_binding else 1)
          map 0
      with
      | (_ : int) -> choose map
      | exception More_than_one_binding -> raise Not_found

  let get_singleton map =
    match get_singleton_exn map with
    | exception Not_found -> None
    | key, datum -> Some (key, datum)

  let keys map = fold (fun k _ set -> Set.add k set) map Set.empty

  let of_set f set = Set.fold (fun e map -> add e (f e) map) set empty
end
[@@inline]

module Make_tbl (T : Thing) = struct
  include Hashtbl.Make [@inlined hint] (T)

  let print print_datum ppf tbl =
    Fmt.pf ppf "@[<1>{@[%a@]}@]"
      (Fmt.iter_bindings ~sep:Fmt.comma iter
         (Fmt.pair ~sep:(Fmt.any " ->@ ") T.print print_datum
         |> Fmt.box ~indent:1))
      tbl
end
[@@inline]

module Make (T : Thing) = struct
  module T = T
  include T
  module Set = Make_set (T)
  module Map = Make_map (T) (Set)
  module Tbl = Make_tbl (T)
end
[@@inline]
