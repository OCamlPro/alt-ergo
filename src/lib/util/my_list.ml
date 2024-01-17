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

let rec assoc eq x = function
  | [] -> raise Not_found
  | (a,b)::l -> if eq a x then b else assoc eq x l

let rec assoc_opt eq x = function
    [] -> None
  | (a,b)::l -> if eq a x then Some b else assoc_opt eq x l

let rec mem_assoc eq x = function
  | [] -> false
  | (a, _) :: l -> eq a x || mem_assoc eq x l

let rec remove_assoc eq x = function
  | [] -> []
  | (a, _ as pair) :: l ->
    if eq a x then l else pair :: remove_assoc eq x l

let apply f l =
  let res, same =
    List.fold_left
      (fun (acc, same) a ->
         let b = f a in
         b :: acc, same && a == b
      )([], true) l
  in
  (if same then l else List.rev res), same

let apply_right f l =
  let res, same =
    List.fold_left
      (fun (acc, same) (v, a) ->
         let b = f a in
         (v, b) :: acc, same && a == b
      )([], true) l
  in
  (if same then l else List.rev res), same

let rec try_map f l =
  match l with
  | [] -> Some []
  | x :: xs ->
    Option.bind (f x) @@ fun y ->
    Option.bind (try_map f xs) @@ fun ys ->
    Some (y :: ys)

let rec is_sorted cmp l =
  match l with
  | x :: y :: xs -> cmp x y <= 0 && is_sorted cmp (y :: xs)
  | [_] | [] -> true

let rec iter_pair f (l1, l2) =
  match l1, l2 with
  | [], [] -> ()
  | hd1 :: tl1, hd2 :: tl2 ->
    f (hd1, hd2);
    iter_pair f (tl1, tl2)
  | _ -> invalid_arg "iter_pair"
