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

module Sy = Symbols
module E  = Expr
module Hs = Hstring

type 'a abstract =
  | Cons of Hs.t * Ty.t
  (* [Cons(hs, ty)] represents a constructor of an enum type of type [ty]. *)

  | Alien of 'a
  (* [Alien r] represents a uninterpreted enum semantic value. *)

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak (X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  let name = "Sum"

  let timer = Modules.M_Sum

  let is_mine_symb sy ty =
    match sy, ty with
    | Sy.Op (Sy.Constr _), Ty.Tsum _ -> true
    | _ -> false

  let fully_interpreted _ = true

  let type_info = function
    | Cons (_, ty) -> ty
    | Alien x -> X.type_info x

  let color _ = assert false


  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Printer

    let print fmt = function
      | Cons (hs,_) -> Format.fprintf fmt "%s" (Hs.view hs)
      | Alien x -> Format.fprintf fmt "%a" X.print x

    let solve_bis a b =
      if Options.get_debug_sum () then
        print_dbg
          ~module_name:"Enum" ~function_name:"solve"
          "@[<v 2>we solve %a = %a@ " X.print a X.print b

    let solve_bis_result res =
      if Options.get_debug_sum () then
        match res with
        | [p,v] ->
          print_dbg ~header:false
            "we get: %a |-> %a@]" X.print p X.print v
        | []    ->
          print_dbg ~header:false
            "the equation is trivial"
        | _ -> assert false

    let solve_bis_unsolvable () =
      if Options.get_debug_sum () then
        print_dbg
          "the equation is unsolvable@]"

  end
  (*BISECT-IGNORE-END*)

  let print = Debug.print

  let embed r =
    match X.extract r with
    | Some c -> c
    | None -> Alien r

  let is_mine = function
    | Alien r -> r
    | Cons _ as c -> X.embed c

  let compare_mine c1 c2 =
    match c1 , c2 with
    | Cons (h1,ty1) , Cons (h2,ty2)  ->
      let n = Hs.compare h1 h2 in
      if n <> 0 then n else Ty.compare ty1 ty2
    | Alien r1, Alien r2 -> X.str_cmp r1 r2
    | Alien _ , Cons _   -> 1
    | Cons _  , Alien _  -> -1

  let compare x y = compare_mine (embed x) (embed y)

  let equal s1 s2 = match s1, s2 with
    | Cons (h1,ty1) , Cons (h2,ty2)  -> Hs.equal h1 h2 && Ty.equal ty1 ty2
    | Alien r1, Alien r2 -> X.equal r1 r2
    | Alien _ , Cons _  | Cons _  , Alien _  -> false

  let hash = function
    | Cons (h, ty) -> Hstring.hash h + 19 * Ty.hash ty
    | Alien r -> X.hash r

  let leaves _ = []

  let is_constant _ = true

  let subst p v c =
    let cr = is_mine c in
    if X.equal p cr then v
    else
      match c with
      | Cons _ -> cr
      | Alien r -> X.subst p v r

  let make t = match E.term_view t with
    | { E.f = Sy.Op (Sy.Constr hs); xs = []; ty; _ } ->
      is_mine (Cons(hs,ty)), []
    | _ ->
      Printer.print_err
        "Enum theory only expect constructors with no arguments; got %a."
        E.print t;
      assert false

  let solve a b =
    match embed a, embed b with
    | Cons(c1,_) , Cons(c2,_) when Hs.equal c1 c2 -> []
    | Cons(_,_) , Cons(_,_) -> raise Util.Unsolvable
    | Cons _     , Alien r2   -> [r2,a]
    | Alien r1   , Cons _     -> [r1,b]
    | Alien _    , Alien _    ->
      if X.str_cmp a b > 0 then [a,b] else [b,a]

  let solve_bis a b =
    Debug.solve_bis a b;
    try
      let res = solve a b in
      Debug.solve_bis_result res;
      res
    with Util.Unsolvable ->
      Debug.solve_bis_unsolvable ();
      raise Util.Unsolvable

  let abstract_selectors v acc = is_mine v, acc

  let term_extract _ = None, false

  let solve r1 r2 pb =
    Sig.{pb with sbt = List.rev_append (solve_bis r1 r2) pb.sbt}

  let assign_value _ _ _ =
    (* As the models of this theory are finite, the case-split
       mechanism can and does exhaust all the possible values.
       Thus we don't need to guess new values here. *)
    None

  let to_model_term r =
    match embed r with
    | Cons (hs, ty) ->
      Some (E.mk_term Sy.(Op (Constr hs)) [] ty)
    | Alien a -> X.to_model_term a
end
