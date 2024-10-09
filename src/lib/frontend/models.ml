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

module Sy = Symbols
module X = Shostak.Combine
module E = Expr
module MS = Map.Make(String)

open Alias.Dolmen

let constraints = ref MS.empty

type t = {
  propositional : Expr.Set.t;
  model : ModelMap.t;
  term_values : Expr.t Expr.Map.t
}

let empty = {
  propositional = Expr.Set.empty;
  model = ModelMap.empty ~suspicious:false [];
  term_values = Expr.Map.empty;
}

module Pp_smtlib_term = struct
  open Format
  let to_string_type t =
    asprintf "%a" Ty.pp_smtlib t

  let rec print fmt t =
    let {Expr.f;xs;ty; _} = Expr.term_view t in
    match f, xs with

    | Sy.Lit lit, xs ->
      begin
        match lit, xs with
        | Sy.L_eq, a::l ->
          if Options.get_output_smtlib () then
            fprintf fmt "(= %a%a)"
              print a (fun fmt -> List.iter (fprintf fmt " %a" print)) l
          else
            fprintf fmt "(%a%a)"
              print a (fun fmt -> List.iter (fprintf fmt " = %a" print)) l

        | Sy.L_neg_eq, [a; b] ->
          if Options.get_output_smtlib () then
            fprintf fmt "(not (= %a %a))" print a print b
          else
            fprintf fmt "(%a <> %a)" print a print b

        | Sy.L_neg_eq, a::l ->
          if Options.get_output_smtlib () then
            fprintf fmt "(distinct %a%a)"
              print a (fun fmt -> List.iter (fprintf fmt " %a" print)) l
          else
            fprintf fmt "distinct(%a%a)"
              print a (fun fmt -> List.iter (fprintf fmt ", %a" print)) l

        | Sy.L_built Sy.LE, [a;b] ->
          if Options.get_output_smtlib () then
            fprintf fmt "(<= %a %a)" print a print b
          else
            fprintf fmt "(%a <= %a)" print a print b

        | Sy.L_built Sy.LT, [a;b] ->
          if Options.get_output_smtlib () then
            fprintf fmt "(< %a %a)" print a print b
          else
            fprintf fmt "(%a < %a)" print a print b

        | Sy.L_neg_built Sy.LE, [a; b] ->
          if Options.get_output_smtlib () then
            fprintf fmt "(> %a %a)" print a print b
          else
            fprintf fmt "(%a > %a)" print a print b

        | Sy.L_neg_built Sy.LT, [a; b] ->
          if Options.get_output_smtlib () then
            fprintf fmt "(>= %a %a)" print a print b
          else
            fprintf fmt "(%a >= %a)" print a print b

        | Sy.L_neg_pred, [a] ->
          fprintf fmt "(not %a)" print a

        | Sy.L_built Sy.BVULE, [a;b] ->
          if Options.get_output_smtlib () then
            fprintf fmt "(bvule %a %a)" print a print b
          else
            fprintf fmt "(%a <= %a)" print a print b

        | Sy.L_neg_built Sy.BVULE, [a;b] ->
          if Options.get_output_smtlib () then
            fprintf fmt "(bvugt %a %a)" print a print b
          else
            fprintf fmt "(%a > %a)" print a print b

        | Sy.L_built (Sy.IsConstr hs), [e] ->
          if Options.get_output_smtlib () then
            fprintf fmt "((_ is %a) %a)" DE.Term.Const.print hs print e
          else
            fprintf fmt "(%a ? %a)" print e DE.Term.Const.print hs

        | Sy.L_neg_built (Sy.IsConstr hs), [e] ->
          if Options.get_output_smtlib () then
            fprintf fmt "(not ((_ is %a) %a))" DE.Term.Const.print hs print e
          else
            fprintf fmt "not (%a ? %a)" print e DE.Term.Const.print hs

        | (Sy.L_built (Sy.LT | Sy.LE | Sy.BVULE)
          | Sy.L_neg_built (Sy.LT | Sy.LE | Sy.BVULE)
          | Sy.L_neg_pred | Sy.L_eq | Sy.L_neg_eq
          | Sy.L_built (Sy.IsConstr _)
          | Sy.L_neg_built (Sy.IsConstr _)) , _ ->
          assert false

      end

    | Sy.Op Sy.Get, [e1; e2] ->
      if Options.get_output_smtlib () then
        fprintf fmt "(select %a %a)" print e1 print e2
      else
        fprintf fmt "%a[%a]" print e1 print e2

    | Sy.Op Sy.Set, [e1; e2; e3] ->
      if Options.get_output_smtlib () then
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
      if Options.get_output_smtlib () then
        fprintf fmt "(%a %a)" DE.Term.Const.print field print e
      else
        fprintf fmt "%a.%a" print e DE.Term.Const.print field

    | Sy.Op (Sy.Record), _ ->
      begin match ty with
        | Ty.Trecord { Ty.lbs = lbs; _ } ->
          assert (List.length xs = List.length lbs);
          fprintf fmt "{";
          ignore (List.fold_left2 (fun first (field,_) e ->
              fprintf fmt "%s%a = %a"  (if first then "" else "; ")
                DE.Term.Const.print field print e;
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
      fprintf fmt "%a(%a)" DE.Term.Const.print hs print_list l

    | Sy.Op _, [e1; e2] ->
      if Options.get_output_smtlib () then
        fprintf fmt "(%a %a %a)" Sy.print f print e1 print e2
      else
        fprintf fmt "(%a %a %a)" print e1 Sy.print f print e2

    | Sy.Op Sy.Destruct hs, [e] ->
      fprintf fmt "%a#%a" print e DE.Term.Const.print hs


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
      if Options.get_output_smtlib () then
        fprintf fmt "(%a %a)" Sy.print f print_list xs
      else
        fprintf fmt "%a(%a)" Sy.print f print_list xs

  and print_list_sep sep fmt = function
    | [] -> ()
    | [t] -> print fmt t
    | t::l -> Format.fprintf fmt "%a%s%a" print t sep (print_list_sep sep) l

  and print_list fmt = print_list_sep "," fmt

end

module Why3CounterExample = struct
  let pp_term fmt t =
    if Options.get_output_format () == Why3 then
      Pp_smtlib_term.print fmt t
    else
      E.print fmt t

  let output_constraints fmt prop_model =
    let assertions = Expr.Set.fold (fun e acc ->
        (Format.dprintf "%t(assert %a)@ " acc pp_term e)
      ) prop_model (Format.dprintf "") in
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

end
(* of module Why3CounterExample *)

let pp ppf { model; propositional; _ } =
  if Options.get_model_type_constraints () then begin
    Why3CounterExample.output_constraints ppf propositional
  end;
  ModelMap.pp ppf model
