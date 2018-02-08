(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* useful option combinators *)
(*
let inhabited = function None -> false | Some _ -> true

let get = function None -> invalid_arg "Why3_opt.get" | Some x -> x

let get_exn exn = function None -> raise exn | Some x -> x

let get_def d = function None -> d | Some x -> x
 *)
let map f = function None -> None | Some x -> Some (f x)
(*
let apply d f x = match f with None -> d | Some f -> f x

let apply2 d f x y = match f with None -> d | Some f -> f x y

let fold f d = function None -> d | Some x -> f d x

let fold_right f o d = match o with None -> d | Some x -> f x d
 *)
let iter f = function None -> () | Some x -> f x
(*
let map2 f x y = match x,y with
  | None, None -> None
  | Some x, Some y -> Some (f x y)
  | _ -> invalid_arg "Why3_opt.map2"

let equal eq a b = match a,b with
  | None, None -> true
  | None, _ | _, None -> false
  | Some x, Some y -> eq x y

let compare cmp a b = match a,b with
  | None, None -> 0
  | None, Some _ -> -1
  | Some _, None -> 1
  | Some x, Some y -> cmp x y

let map_fold f acc x = match x with
  | None -> acc, None
  | Some x -> let acc, x = f acc x in acc, Some x*)
