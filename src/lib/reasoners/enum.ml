(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Options
open Format
open Sig

module Sy = Symbols
module E  = Expr
module Hs = Hstring

type 'a abstract = Cons of Hs.t * Ty.t |  Alien of 'a

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak (X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  let name = "Sum"

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

    let print fmt = function
      | Cons (hs,_) -> fprintf fmt "%s" (Hs.view hs)
      | Alien x -> fprintf fmt "%a" X.print x

    let solve_bis a b =
      if debug_sum () then fprintf fmt "[Sum] we solve %a = %a@."
          X.print a X.print b

    let solve_bis_result res =
      if debug_sum () then
        match res with
        | [p,v] -> fprintf fmt "\twe get: %a |-> %a@." X.print p X.print v
        | []    -> fprintf fmt "\tthe equation is trivial@."
        | _ -> assert false

    let solve_bis_unsolvable () =
      if debug_sum () then fprintf fmt "\tthe equation is unsolvable@."

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

  let subst p v c =
    let cr = is_mine c in
    if X.equal p cr then v
    else
      match c with
      | Cons _ -> cr
      | Alien r    -> X.subst p v r

  let make t = match E.term_view t with
    | E.Term { E.f = Sy.Op (Sy.Constr hs); xs = []; ty; _ } ->
      is_mine (Cons(hs,ty)), []
    | _ -> assert false

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
    {pb with sbt = List.rev_append (solve_bis r1 r2) pb.sbt}

  let solve r1 r2 pb =
    if Options.timers() then
      try
        Timers.exec_timer_start Timers.M_Sum Timers.F_solve;
        let res = solve r1 r2 pb in
        Timers.exec_timer_pause Timers.M_Sum Timers.F_solve;
        res
      with e ->
        Timers.exec_timer_pause Timers.M_Sum Timers.F_solve;
        raise e
    else solve r1 r2 pb

  let assign_value _ _ _ =
    (* values of theory sum should be assigned by case_split *)
    None

  let choose_adequate_model _ r l =
    let l =
      List.filter
        (fun (_, r) -> match embed r with Cons _ -> true | _ -> false) l
    in
    let r = match l with
      | (_,r)::l ->
        List.iter (fun (_,x) -> assert (X.equal x r)) l;
        r

      | [] ->
        (* We do this, because terms of some semantic values created
           by CS are not created and added to UF *)
        match embed r with Cons _ -> r | _ -> assert false
    in
    ignore (flush_str_formatter ());
    fprintf str_formatter "%a" print (embed r);
    r, flush_str_formatter ()

end

