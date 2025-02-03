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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type name_space = Internal | Fresh | Fresh_ac | Skolem | Abstract

module Make () = struct
  let fresh, reset_fresh_cpt =
    let cpt = ref 0 in
    let fresh_string ?(base = "") () =
      let res = base ^ (string_of_int !cpt) in
      incr cpt;
      res
    in
    let reset_fresh_string_cpt () =
      cpt := 0
    in
    fresh_string, reset_fresh_string_cpt
end

module Internal = Make ()
module Skolem = Make ()
module Abstract = Make ()

type t =
  | Term_cst of { tcst : Dolmen.Std.Expr.term_cst; defined : bool }
  | Hstring of { hs : Hstring.t; ns : name_space }

let mangle ns s =
  match ns with
  | Internal -> ".!" ^ s
  | Fresh -> ".k" ^ s
  | Fresh_ac -> ".K" ^ s
  | Skolem -> ".?__" ^ s
  | Abstract -> "@a" ^ s

let of_term_cst ?(defined = false) tcst =
  (* If the name we got from the user starts with either "."
     or "@" (which are prefixes reserved for solver use in the SMT-LIB
     standard), the name will be printed with an extra ".". So if the user
     writes ".x" or "@x", it will be printed as "..x" and ".@x" instead.

     Normally, this should not occur, but we do this to ensure no confusion
     even if invalid names ever sneak through. *)
  assert (
    let s = Util.show_term_cst tcst in
    not (Compat.String.starts_with ~prefix:"." s) &&
    not (Compat.String.starts_with ~prefix:"@" s));
  Term_cst { tcst; defined }

let of_string ~ns s =
  let () =
    match ns with
    | Fresh | Fresh_ac | Abstract -> invalid_arg "of_string"
    | _ -> ()
  in
  let hs = Hstring.make (mangle ns s) in
  Hstring { hs; ns }

let fresh ?base ~ns () =
  let s =
    match ns with
    | Skolem -> Skolem.fresh ?base ()
    | Abstract -> Abstract.fresh ?base ()
    | _ -> Internal.fresh ?base ()
  in
  let hs = Hstring.make (mangle ns s) in
  Hstring { hs; ns }

let compare i1 i2 =
  match i1, i2 with
  | Term_cst { tcst = t1; defined = d1 },
    Term_cst { tcst = t2; defined = d2 } ->
    let c = Bool.compare d1 d2 in
    if c <> 0 then c
    else Dolmen.Std.Expr.Term.Const.compare t1 t2
  | Term_cst _, _ -> 1
  | _, Term_cst _ -> -1

  | Hstring { hs = hs1; _ }, Hstring { hs = hs2; _ } ->
    (* NB: Internal identifiers are pre-mangled, which means that we do not
       need to take the name space into consideration when comparing. *)
    Hstring.compare hs1 hs2

let equal i1 i2 =
  match i1, i2 with
  | Term_cst { tcst = t1; defined = d1 },
    Term_cst { tcst = t2; defined = d2 } ->
    Bool.equal d1 d2 && Dolmen.Std.Expr.Term.Const.equal t1 t2
  | Hstring { hs = hs1; _ }, Hstring { hs = hs2; _ } ->
    (* NB: Internal identifiers are pre-mangled, which means that we do not
       need to take the name space into consideration when comparing. *)
    Hstring.equal hs1 hs2
  | _ -> false

let hash i =
  match i with
  | Term_cst { tcst; _ } ->
    Dolmen.Std.Expr.Term.Const.hash tcst
  | Hstring { hs; _ } ->
    (* NB: Internal identifiers are pre-mangled, which means that we do not
       need to take the name space into consideration when hashing. *)
    Hstring.hash hs

let pp ppf i =
  match i with
  | Term_cst { tcst; _ } -> Util.pp_term_cst ppf tcst
  | Hstring { hs; _ } ->
    (* Names are pre-mangled *)
    Dolmen.Smtlib2.Script.Poly.Print.id ppf
    @@ Dolmen.Std.Name.simple @@ Hstring.view hs

let show = Fmt.to_to_string pp

let is_suspicious i =
  match i with
  | Term_cst _ -> false
  | Hstring { hs; _ } ->
    match Hstring.view hs with
    | "@/" | "@%" | "@*" -> true
    | _ -> false

let reinit () =
  Internal.reset_fresh_cpt ();
  Skolem.reset_fresh_cpt ();
  Abstract.reset_fresh_cpt ()

module Set = Set.Make (struct
    type nonrec t = t
    let compare = compare
  end)

module Map = Map.Make (struct
    type nonrec t = t
    let compare = compare
  end)
