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

let is_empty = function
  | [] -> true
  | _ -> false

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

let rec find_opt pred l =
  match l with
  | [] -> None
  | e :: r ->
    if pred e then Some e
    else find_opt pred r

let to_seq l =
  let rec aux l () = match l with
    | [] -> Seq.Nil
    | x :: tail -> Seq.Cons (x, aux tail)
  in
  aux l

(* TODO: This function is supported by the Stdlib from OCaml 4.12. *)
let rec compare cmp l1 l2 =
  match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | hd1::tl1, hd2::tl2 ->
    let c = cmp hd1 hd2 in
    if c <> 0 then c
    else
      compare cmp tl1 tl2

(* List.equal in OCaml 4.12+ *)
let rec equal eq l1 l2 =
  match l1, l2 with
  | [], [] -> true
  | hd1 :: tl1, hd2 :: tl2 when eq hd1 hd2 -> equal eq tl1 tl2
  | _ -> false

let partition_map ?(keep_ordering=true) f l =
  let rec part left right = function
    | [] ->
      if keep_ordering then List.rev left, List.rev right
      else left, right
    | x :: l ->
      let left, right =
        match f x with
        | Ok x   -> x :: left, right
        | Error x -> left, x :: right
      in
      part left right l
  in
  part [] [] l
