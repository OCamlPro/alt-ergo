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

open Format
open Options

module X = Shostak.Combine

module Ac = Shostak.Ac
module Ex = Explanation

module Sy = Symbols
module E = Expr
module ME = Expr.Map
module SE = Expr.Set
module MS = Map.Make(String)
module MX = Shostak.MXH

let constraints = ref MS.empty

type t = {
  propositional : Expr.Set.t;
  model : ModelMap.t;
  terms_values : (Shostak.Combine.r * string) Expr.Map.t
}

let empty = {
  propositional = Expr.Set.empty;
  model = ModelMap.create [];
  terms_values = Expr.Map.empty;
}

module Pp_smtlib_term = struct

  let to_string_type t =
    asprintf "%a" Ty.pp_smtlib t

  let rec print fmt t =
    let {E.f;xs;ty; _} = E.term_view t in
    match f, xs with

    | Sy.Lit lit, xs ->
      begin
        match lit, xs with
        | Sy.L_eq, a::l ->
          if get_output_smtlib () then
            fprintf fmt "(= %a%a)"
              print a (fun fmt -> List.iter (fprintf fmt " %a" print)) l
          else
            fprintf fmt "(%a%a)"
              print a (fun fmt -> List.iter (fprintf fmt " = %a" print)) l

        | Sy.L_neg_eq, [a; b] ->
          if get_output_smtlib () then
            fprintf fmt "(not (= %a %a))" print a print b
          else
            fprintf fmt "(%a <> %a)" print a print b

        | Sy.L_neg_eq, a::l ->
          if get_output_smtlib () then
            fprintf fmt "(distinct %a%a)"
              print a (fun fmt -> List.iter (fprintf fmt " %a" print)) l
          else
            fprintf fmt "distinct(%a%a)"
              print a (fun fmt -> List.iter (fprintf fmt ", %a" print)) l

        | Sy.L_built Sy.LE, [a;b] ->
          if get_output_smtlib () then
            fprintf fmt "(<= %a %a)" print a print b
          else
            fprintf fmt "(%a <= %a)" print a print b

        | Sy.L_built Sy.LT, [a;b] ->
          if get_output_smtlib () then
            fprintf fmt "(< %a %a)" print a print b
          else
            fprintf fmt "(%a < %a)" print a print b

        | Sy.L_neg_built Sy.LE, [a; b] ->
          if get_output_smtlib () then
            fprintf fmt "(> %a %a)" print a print b
          else
            fprintf fmt "(%a > %a)" print a print b

        | Sy.L_neg_built Sy.LT, [a; b] ->
          if get_output_smtlib () then
            fprintf fmt "(>= %a %a)" print a print b
          else
            fprintf fmt "(%a >= %a)" print a print b

        | Sy.L_neg_pred, [a] ->
          fprintf fmt "(not %a)" print a

        | Sy.L_built (Sy.IsConstr hs), [e] ->
          if get_output_smtlib () then
            fprintf fmt "((_ is %a) %a)" Hstring.print hs print e
          else
            fprintf fmt "(%a ? %a)" print e Hstring.print hs

        | Sy.L_neg_built (Sy.IsConstr hs), [e] ->
          if get_output_smtlib () then
            fprintf fmt "(not ((_ is %a) %a))" Hstring.print hs print e
          else
            fprintf fmt "not (%a ? %a)" print e Hstring.print hs

        | (Sy.L_built (Sy.LT | Sy.LE) | Sy.L_neg_built (Sy.LT | Sy.LE)
          | Sy.L_neg_pred | Sy.L_eq | Sy.L_neg_eq
          | Sy.L_built (Sy.IsConstr _)
          | Sy.L_neg_built (Sy.IsConstr _)) , _ ->
          assert false

      end

    | Sy.Op Sy.Get, [e1; e2] ->
      if get_output_smtlib () then
        fprintf fmt "(select %a %a)" print e1 print e2
      else
        fprintf fmt "%a[%a]" print e1 print e2

    | Sy.Op Sy.Set, [e1; e2; e3] ->
      if get_output_smtlib () then
        fprintf fmt "(store %a %a %a)"
          print e1
          print e2
          print e3
      else
        fprintf fmt "%a[%a<-%a]" print e1 print e2 print e3

    | Sy.Op Sy.Concat, [e1; e2] ->
      fprintf fmt "%a@@%a" print e1 print e2

    | Sy.Op Sy.Extract (i, j), [e] ->
      fprintf fmt "%a^{%d,%d}" print e i j

    | Sy.Op (Sy.Access field), [e] ->
      if get_output_smtlib () then
        fprintf fmt "(%s %a)" (Hstring.view field) print e
      else
        fprintf fmt "%a.%s" print e (Hstring.view field)

    | Sy.Op (Sy.Record), _ ->
      begin match ty with
        | Ty.Trecord { Ty.lbs = lbs; _ } ->
          assert (List.length xs = List.length lbs);
          fprintf fmt "{";
          ignore (List.fold_left2 (fun first (field,_) e ->
              fprintf fmt "%s%s = %a"  (if first then "" else "; ")
                (Hstring.view field) print e;
              false
            ) true lbs xs);
          fprintf fmt "}";
        | _ -> assert false
      end

    (* TODO: introduce PrefixOp in the future to simplify this ? *)
    | Sy.Op op, [e1; e2] when op == Sy.Pow || op == Sy.Integer_round ||
                              op == Sy.Max_real || op == Sy.Max_int ||
                              op == Sy.Min_real || op == Sy.Min_int ->
      fprintf fmt "%a(%a,%a)" Sy.print f print e1 print e2

    (* TODO: introduce PrefixOp in the future to simplify this ? *)
    | Sy.Op (Sy.Constr hs), ((_::_) as l) ->
      fprintf fmt "%a(%a)" Hstring.print hs print_list l

    | Sy.Op _, [e1; e2] ->
      if get_output_smtlib () then
        fprintf fmt "(%a %a %a)" Sy.print f print e1 print e2
      else
        fprintf fmt "(%a %a %a)" print e1 Sy.print f print e2

    | Sy.Op Sy.Destruct (hs, grded), [e] ->
      fprintf fmt "%a#%s%a"
        print e (if grded then "" else "!") Hstring.print hs


    | Sy.In(lb, rb), [t] ->
      fprintf fmt "(%a in %a, %a)" print t Sy.print_bound lb Sy.print_bound rb

    | Sy.Name { hs = n; _ }, l -> begin
        let constraint_name =
          try let constraint_name,_,_ =
                (MS.find (Hstring.view n) !constraints) in
            constraint_name
          with _ ->
            let constraint_name = "c_"^(Hstring.view n)  in
            constraints := MS.add (Hstring.view n)
                (constraint_name,
                 to_string_type (E.type_info t),
                 List.map (fun e -> to_string_type (E.type_info e)) l
                ) !constraints;
            constraint_name
        in
        match l with
        | [] -> fprintf fmt "%s" constraint_name
        | l ->
          fprintf fmt "(%s %a)" constraint_name (Printer.pp_list_space print) l;
      end

    | _, [] ->
      fprintf fmt "%a" Sy.print f

    | _, _ ->
      if get_output_smtlib () then
        fprintf fmt "(%a %a)" Sy.print f print_list xs
      else
        fprintf fmt "%a(%a)" Sy.print f print_list xs

  and print_list_sep sep fmt = function
    | [] -> ()
    | [t] -> print fmt t
    | t::l -> Format.fprintf fmt "%a%s%a" print t sep (print_list_sep sep) l

  and print_list fmt = print_list_sep "," fmt

end

(* of module SmtlibCounterExample *)
(*
module Why3CounterExample = struct

  let output_constraints fmt prop_model =
    let assertions = SE.fold (fun e acc ->
        (dprintf "%t(assert %a)@ " acc SmtlibCounterExample.pp_term e)
      ) prop_model (dprintf "") in
    Format.fprintf fmt "@ ; constraints@ ";
    MS.iter (fun _ (name,ty,args_ty) ->
        match args_ty with
        | [] ->
          Format.fprintf fmt "(declare-const %s %s)@ "
            name ty
        | l ->
          Format.fprintf fmt "(declare-fun %s (%s) %s)@ "
            name
            (String.concat " " l)
            ty
      ) !constraints;
    Format.fprintf fmt "@ ; assertions@ ";
    Format.fprintf fmt "%t" assertions

end *)
(* of module Why3CounterExample *)

let pp ppf { model; _ } = ModelMap.pp ppf model

(* let pp_constant ppf (_sy, t) =
   Fmt.pf ppf "%a" SmtlibCounterExample.pp_abstract_value_of_type t *)

(* let output_concrete_model fmt props ~functions ~constants ~arrays =
   if ModelMap.(is_suspicious functions || is_suspicious constants
               || is_suspicious arrays) then
    Format.fprintf fmt "; This model is a best-effort. It includes symbols
        for which model generation is known to be incomplete. @.";

   Format.fprintf fmt "@[<v 2>(";
   if Options.get_model_type_constraints () then begin
    Why3CounterExample.output_constraints fmt m.propositional
   end;

   let values = Hashtbl.create 17 in
   let find_or_add sy f =
    try Hashtbl.find values sy
    with Not_found ->
      let value = f () in
      Hashtbl.replace values sy value;
      value
   in
   (* Add the constants *)
   ModelMap.iter (fun (f, xs_ty, _) st ->
      assert (Lists.is_empty xs_ty);
      ModelMap.V.iter (fun (keys, (value_r, value_s)) ->
          assert (Lists.is_empty keys);
          Hashtbl.add values f (value (value_r, value_s))
        ) st
    ) m.constants;

   (* Add the arrays values, when applicable *)
   ModelMap.iter (fun (f, xs_ty, ty) st ->
      let root =
        try Hashtbl.find values f
        with Not_found -> Constant (f, Tfarray (List.hd xs_ty, ty))
      in
      Hashtbl.replace values f @@
      ModelMap.V.fold (fun (keys, rs) acc ->
          Store (acc, value (snd (List.hd keys)), value rs)) st root
    ) m.arrays;

   let pp_value =
    pp_value (fun ppf (sy, ty) ->
        let v =
          find_or_add sy @@ fun () ->
          (* NB: It is important that we call `pp_abstract_value_of_type`
             immediately (not in a delayed fashion) so that we make sure that
             the same abstract value will get printed each time. *)
          Abstract (
            Fmt.to_to_string SmtlibCounterExample.pp_abstract_value_of_type ty)
        in
        pp_value pp_constant ppf v)
   in

   let pp_x ppf xs = pp_value ppf (value xs) in

   (* Functions *)
   let records =
    SmtlibCounterExample.output_functions_counterexample
      pp_x fmt MS.empty m.functions
   in

   (* Constants *)
   SmtlibCounterExample.output_constants_counterexample
    pp_x fmt records m.constants;

   (* Arrays *)
   (*     SmtlibCounterExample.output_arrays_counterexample fmt m.arrays; *)

  Printer.print_fmt fmt "@]@,)" *)
