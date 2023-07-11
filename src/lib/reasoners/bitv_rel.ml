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

module E = Expr
module X = Shostak.Combine

type t = unit

let as_int2bv r =
  match X.term_extract r with
  | Some t, _ ->
    begin match E.term_view t with
      | { f = Op Int2BV n ; xs = [ t ] ; _ } -> Some (t, n)
      | _ -> None
    end
  | _ -> None

let empty _ = ()
let assume env _uf inputs =
  let assume =
    List.fold_left (fun acc (xview, _, ex, origin) ->
        match xview with
        | Xliteral.Eq (t, u) ->
          (* ((_ int2bv n) t) and ((_ int2bv n) u) are equal iff t and u are
             congruent modulo [pow 2 n].

             Note that we use [(t - u) mod 2^n = 0] because we introduce a
             single auxiliary variable in that case, wherease using the
             equality of [t mod 2^n] and [u mod 2^n] would introduce two and
             make things harder for the arithmetic reasoner. *)
          begin match as_int2bv t, as_int2bv u with
            | Some (t, n), Some (u, m) ->
              assert (n = m);
              let eq =
                E.Ints.(E.Core.eq ((t - u) mod ~$Z.(pow ~$2 n)) ~$$0)
              in
              (Sig_rel.LTerm eq, ex, origin) :: acc
            | _ -> acc
          end
        | Xliteral.Distinct (neg, ts) ->
          (* ((_ int2bv n) t) and ((_ int2bv n) u) are distinct iff t and u are
             *not* congruent modulo [pow 2 n] *)
          let mk =
            if neg then E.Core.eq
            else fun s t -> E.Core.(not (eq s t))
          in
          let ts = List.filter_map as_int2bv ts in
          let rec aux acc = function
            | [] -> acc
            | (t, n) :: ts ->
              let acc =
                List.fold_left (fun acc (u, m) ->
                    assert (n = m);
                    let rel =
                      E.Ints.(mk ((t - u) mod ~$Z.(pow ~$2 n)) ~$$0)
                    in
                    (Sig_rel.LTerm rel, ex, origin) :: acc) acc ts
              in
              aux acc ts
          in aux acc ts
        | _ -> acc)
      [] inputs
  in
  env, { Sig_rel.assume; remove = []}
let query _ _ _ = None
let case_split _ _ ~for_model:_ = []
let add env _uf _r _t = env, []
let new_terms _ = Expr.Set.empty
let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Bitv ->
    failwith "This Theory does not support theories extension"
  | _ -> t
