(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

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

let rrmap f l = List.rev (List.map f l)

let rec find_opt pred l =
  match l with
  | [] -> None
  | e :: r ->
    if pred e then Some e
    else find_opt pred r

