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

module E = Expr
module Sy = Symbols

type 'r abstract =
  | Alien of 'r
  | Literal of Ty.t * Fp_value.t

module Shostak (X : sig
  include Sig.X

  val extract : r -> r abstract option

  val embed : r abstract -> r
end) =
struct
  type t = X.r abstract

  type r = X.r

  let name = "Fpa"

  let timer = Timers.M_Fpa

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    let solve r1 r2 =
      if Options.get_debug_fpa () > 0
      then
        Printer.print_dbg ~module_name:"Fpa" ~function_name:"solve"
          "solve %a = %a" X.print r1 X.print r2

    let unsolvable r1 r2 =
      if Options.get_debug_fpa () > 0
      then
        Printer.print_dbg ~module_name:"Fpa" ~function_name:"solve"
          "%a <> %a: distinct literals, unsolvable" X.print r1 X.print r2
  end
  (*BISECT-IGNORE-END*)

  let is_mine_symb = function
    | Sy.Float _ -> Options.get_smt_lib_fpa ()
    | _ -> false

  let embed r = match X.extract r with Some v -> v | None -> Alien r

  let is_mine v = X.embed v

  let make t =
    let { E.f; ty; _ } = E.term_view t in
    match f with
    | Sy.Float fp_val -> is_mine (Literal (ty, fp_val)), []
    | _ ->
    | _ -> Util.internal_error "%a is not a floating-point literal" E.print t

  let type_info = function Alien r -> X.type_info r | Literal (ty, _) -> ty

  let equal s1 s2 =
    match s1, s2 with
    | Alien r1, Alien r2 -> X.equal r1 r2
    | Literal (ty1, v1), Literal (ty2, v2) ->
      Ty.equal ty1 ty2 && Fp_value.equal v1 v2
    | _ -> false

  let hash = function
    | Alien r -> X.hash r
    | Literal (ty, v) -> Ty.hash ty + (17 * Hashtbl.hash v)

  let compare s1 s2 =
    match embed s1, embed s2 with
    | Alien r1, Alien r2 -> X.str_cmp r1 r2
    | Alien _, _ -> 1
    | _, Alien _ -> -1
    | Literal (ty1, v1), Literal (ty2, v2) ->
      let c = Ty.compare ty1 ty2 in
      if c <> 0 then c else Fp_value.compare v1 v2

  let print ppf = function
    | Alien r -> X.print ppf r
    | Literal (Ty.Tfloat (eb, sb), v) -> Fp_value.pp_smtlib eb sb ppf v
    | Literal _ -> assert false

  let leaves = function Alien r -> X.leaves r | Literal _ -> []

  let is_constant = function Alien r -> X.is_constant r | Literal _ -> true

  let subst p v t =
    match t with
    | Literal _ -> is_mine t
    | Alien r -> if X.equal p r then v else X.subst p v r

  let fully_interpreted = function
    | Sy.Float _ -> Options.get_smt_lib_fpa ()
    | _ -> false

  let abstract_selectors t acc =
    match t with Literal _ -> is_mine t, acc | Alien _ -> assert false

  let color _ = assert false

  let term_extract r =
    match embed r with
    | Literal (Ty.Tfloat (eb, sb), fp_val) -> Some (E.float fp_val eb sb), false
    | Literal _ -> assert false
    | Alien _ -> None, false

  let solve r1 r2 pb =
    Debug.solve r1 r2;
    match embed r1, embed r2 with
    | Literal (_, l1), Literal (_, l2) ->
      if Fp_value.equal l1 l2
      then pb
      else (
        Debug.unsolvable r1 r2;
        raise Util.Unsolvable)
    | Alien _, Alien _ ->
      Sig.
        { pb with
          sbt = (if X.str_cmp r1 r2 > 0 then r1, r2 else r2, r1) :: pb.sbt
        }
    | Alien _, Literal _ -> Sig.{ pb with sbt = (r1, r2) :: pb.sbt }
    | Literal _, Alien _ -> Sig.{ pb with sbt = (r2, r1) :: pb.sbt }

  let assign_value _ _ _ = None

  let to_model_term r =
    match embed r with
    | Literal (Ty.Tfloat (eb, sb), fp_val) -> Some (E.float fp_val eb sb)
    | Literal _ -> assert false
    | Alien _ -> None
end
