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

open AltErgoLib
open Format
open Numbers
open Options
open Simplex

module MAKE (C : sig
    type t
    val compare : t -> t -> int
    val print : formatter -> t -> unit
  end) = struct

  module MI = Map.Make (struct type t = int let compare a b = a - b end)
  module MD = Map.Make(C)

  let ppprint fmt p =
    MI.iter (fun i q -> fprintf fmt "%s*L%d + " (Q.to_string q) i) p;
    fprintf fmt "0"

  let print_sum id sum =
    fprintf fmt "@.sum %d@." id;
    MD.iter
      (fun x (lp,ln,q) ->
         fprintf fmt "%a -> (%a) + (%a) + %s = 0@."
           C.print x ppprint lp ppprint ln (Q.to_string q)) sum

  module SM = Map.Make
      (struct
        type t1 = (Q.t MI.t * Q.t MI.t * Q.t) MD.t
        type t2 = Q.t MI.t
        type t3 = Q.t MI.t
        type t  = t1 * t2 * t3

        let cmp (m1,n1,q1) (m2,n2,q2) =
          let c = Q.compare q1 q2 in
          if c <> 0 then c
          else
            let c = MI.compare Q.compare m1 m2 in
            if c <> 0 then c
            else MI.compare Q.compare n1 n2

        let compare (sum1, ctt1, lambdas1) (sum2, ctt2, lambdas2) =
          let c = MD.compare cmp sum1 sum2 in
          if c <> 0 then c
          else
            let c = MI.compare Q.compare lambdas1 lambdas2 in
            if c <> 0 then(
              print_sum 1 sum1;
              print_sum 2 sum2;
              fprintf fmt "l1 = %a@." ppprint lambdas1;
              fprintf fmt "l2 = %a@." ppprint lambdas2);
            assert (c = 0);
            c
      end)


  let (m :  (int * result * Q.t MI.t) SM.t ref)      = ref SM.empty
  let (mm : (int * result * Q.t MI.t) SM.t MD.t ref) = ref MD.empty

  let mi_of_l l = List.fold_left (fun m (i,q) -> MI.add i q m) MI.empty l

  let make_repr max_ctt equas s_neq =
    let max_ctt = mi_of_l max_ctt in
    let s_neq   = mi_of_l s_neq in
    let equas =
      List.fold_left
        (fun mp (x, (lp, ln, q)) ->
           let lp = mi_of_l lp in
           let ln = mi_of_l ln in
           MD.add x (lp, ln, q) mp
        )MD.empty equas
    in
    max_ctt, equas, s_neq


  let already_registered max_ctt equas s_neq =
    let repr = equas, max_ctt, s_neq in
    try
      let counter, res_sim, ctt = SM.find repr !m in
      Some (counter, res_sim, ctt)
    with Not_found -> None

  let register max_ctt equas s_neq cpt sim_res =
    if already_registered max_ctt equas s_neq == None then begin
      let repr = equas, max_ctt, s_neq in
      m := SM.add repr (cpt, sim_res, max_ctt) !m
    end

  let already_registered_mon x max_ctt equas s_neq =
    let repr = equas, max_ctt, s_neq in
    try
      let m = MD.find x !mm in
      let counter, res_sim, ctt = SM.find repr m in
      Some (counter, res_sim, ctt)
    with Not_found -> None

  let register_mon x max_ctt equas s_neq cpt sim_res =
    if already_registered_mon x max_ctt equas s_neq == None then begin
      let m = try MD.find x !mm with Not_found -> SM.empty in
      let repr = equas, max_ctt, s_neq in
      mm := MD.add x (SM.add repr (cpt, sim_res, max_ctt) m) !mm
    end

end
