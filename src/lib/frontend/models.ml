(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2020-2020 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

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

let constraints = ref MS.empty

module Pp_smtlib_term = struct

  let to_string_type t =
    asprintf "%a" Ty.print t

  let rec print fmt ({ top_sy; args; ty; _ } as t : E.t) =
    match top_sy, args with
    | Sy.Lit lit, args ->
      begin
        match lit, args with
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

    | Sy.Op Sy.Extract, [e1; e2; e3] ->
      fprintf fmt "%a^{%a,%a}" print e1 print e2 print e3

    | Sy.Op (Sy.Access field), [e] ->
      if get_output_smtlib () then
        fprintf fmt "(%s %a)" (Hstring.view field) print e
      else
        fprintf fmt "%a.%s" print e (Hstring.view field)

    | Sy.Op (Sy.Record), _ ->
      begin match ty with
        | Ty.Trecord { Ty.lbs = lbs; _ } ->
          assert (List.length args = List.length lbs);
          fprintf fmt "{";
          ignore (List.fold_left2 (fun first (field,_) e ->
              fprintf fmt "%s%s = %a"  (if first then "" else "; ")
                (Hstring.view field) print e;
              false
            ) true lbs args);
          fprintf fmt "}";
        | _ -> assert false
      end

    (* TODO: introduce PrefixOp in the future to simplify this ? *)
    | Sy.Op op, [e1; e2] when op == Sy.Pow || op == Sy.Integer_round ||
                              op == Sy.Max_real || op == Sy.Max_int ||
                              op == Sy.Min_real || op == Sy.Min_int ->
      fprintf fmt "%a(%a,%a)" Sy.print top_sy print e1 print e2

    (* TODO: introduce PrefixOp in the future to simplify this ? *)
    | Sy.Op (Sy.Cstr hs), ((_::_) as l) ->
      fprintf fmt "%a(%a)" Hstring.print hs print_list l

    | Sy.Op _, [e1; e2] ->
      if get_output_smtlib () then
        fprintf fmt "(%a %a %a)" Sy.print top_sy print e1 print e2
      else
        fprintf fmt "(%a %a %a)" print e1 Sy.print top_sy print e2

    | Sy.Op Sy.Dstr (hs, grded), [e] ->
      fprintf fmt "%a#%s%a"
        print e (if grded then "" else "!") Hstring.print hs


    | Sy.In(lb, rb), [t] ->
      fprintf fmt "(%a in %a, %a)" print t Sy.Bound.print lb Sy.Bound.print rb

    | Sy.Name (n,_), l -> begin
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
      fprintf fmt "%a" Sy.print top_sy

    | _, _ ->
      if get_output_smtlib () then
        fprintf fmt "(%a %a)" Sy.print top_sy print_list args
      else
        fprintf fmt "%a(%a)" Sy.print top_sy print_list args

  and print_list_sep sep fmt = function
    | [] -> ()
    | [t] -> print fmt t
    | t::l -> Format.fprintf fmt "%a%s%a" print t sep (print_list_sep sep) l

  and print_list fmt = print_list_sep "," fmt

end

module SmtlibCounterExample = struct

  let x_print fmt (_ , ppr) = fprintf fmt "%s" ppr

  let pp_term fmt t =
    if Options.get_output_format () == Why3 then
      Pp_smtlib_term.print fmt t
    else
      E.print fmt t

  let dummy_value_of_type ty =
    match ty with
      Ty.Tint -> "0"
    | Ty.Treal -> "0.0"
    | Ty.Tbool -> "false"
    | _ -> asprintf "%a" pp_term (Expr.fresh_name ~ty)

  let pp_dummy_value_of_type fmt ty =
    if not (Options.get_interpretation_use_underscore ()) then
      let d = dummy_value_of_type ty in
      fprintf fmt "%s " d
    else
      fprintf fmt "_ "

  let add_records_destr records record_name destr_name rep =
    let destrs =
      try MS.find record_name records
      with Not_found -> MS.empty
    in
    let destrs =
      MS.add destr_name rep destrs in
    MS.add record_name destrs records

  let mk_records_constr records record_name
      { Ty.name = _n; record_cstr = cstr; lbs = lbs; _} =
    let find_destrs destr destrs =
      try let rep = MS.find destr destrs in
        Some rep
      with Not_found -> None
    in

    let print_destr fmt (destrs,lbs) =
      List.iter (fun (destr, ty_destr) ->
          let destr = Hstring.view destr in
          match find_destrs destr destrs with
          | None ->
            pp_dummy_value_of_type fmt ty_destr
          | Some rep -> fprintf fmt "%s " rep
        ) lbs
    in
    let destrs =
      try MS.find (Sy.to_string record_name) records
      with Not_found -> MS.empty
    in
    asprintf "%s %a"
      (Hstring.view cstr)
      print_destr (destrs,lbs)

  let add_record_constr records record_name
      { Ty.name = _n; record_cstr = _cstr; lbs = lbs; _} xs_values =
    List.fold_left2(fun records (destr,_) (rep,_) ->
        add_records_destr
          records
          record_name
          (Hstring.view destr)
          (asprintf "%a" pp_term rep)
      ) records lbs xs_values

  let check_records records xs_ty_named xs_values f ty rep =
    match xs_ty_named with
    | [Ty.Trecord _r, _arg] -> begin
        match xs_values with
        | [record_name,_] ->
          add_records_destr
            records
            (asprintf "%a" Expr.print record_name)
            (Sy.to_string f)
            rep
        | [] | _ -> records
      end
    | _ ->
      match ty with
      | Ty.Trecord r ->
        add_record_constr records rep r xs_values
      | _ -> records

  let print_fun_def fmt name args ty t =
    let print_args fmt (ty,name) =
      Format.fprintf fmt "(%s %a)" name Ty.print ty in
    let defined_value =
      try
        let res,_,_ = (MS.find (Sy.to_string name) !constraints) in res
      with _ -> t
    in

    Printer.print_fmt ~flushed:false fmt
      "(define-fun %a (%a) %a %s)@ "
      Sy.print name
      (Printer.pp_list_space (print_args)) args
      Ty.print ty
      defined_value

  let output_constants_counterexample fmt records cprofs =
    ModelMap.iter
      (fun (f, xs_ty, ty) st ->
         assert (xs_ty == []);
         match ModelMap.V.elements st with
         | [[], rep] ->
           let rep = Format.asprintf "%a" x_print rep in
           let rep =
             match ty with
             | Ty.Trecord r ->
               let constr = mk_records_constr records f r in
               sprintf "(%s)" constr
             | _ -> rep
           in

           print_fun_def fmt f [] ty rep
         | _ -> assert false
      ) cprofs

  let output_functions_counterexample fmt records fprofs =
    let  records = ref records in
    ModelMap.iter
      (fun (f, xs_ty, ty) st ->
         let xs_ty_named = List.mapi (fun i ty ->
             ty,(sprintf "arg_%d" i)
           ) xs_ty in

         let rep =
           let representants =
             ModelMap.V.fold (fun (xs_values,(_rep,srep)) acc ->
                 assert ((List.length xs_ty_named) = (List.length xs_values));
                 records :=
                   check_records !records xs_ty_named xs_values f ty srep;
                 let reps = try MS.find srep acc with Not_found -> [] in
                 MS.add srep (xs_values :: reps) acc
               ) st MS.empty in

           let representants = MS.fold (fun srep xs_values_list acc ->
               (srep,xs_values_list) :: acc) representants [] in

           let rec mk_ite_and xs tys =
             match xs, tys with
             | [],[] -> assert false
             | [xs,_],[_ty,name] ->
               asprintf "(= %s %a)" name pp_term xs
             | (xs,_) :: l1, (_ty,name) :: l2 ->
               asprintf "(and (= %s %a) %s)"
                 name
                 pp_term xs
                 (mk_ite_and l1 l2)
             | _, _ -> assert false
           in

           let mk_ite_or l =
             let pp_or_list fmt xs_values =
               fprintf fmt "%s" (mk_ite_and xs_values xs_ty_named)
             in
             match l with
             | [] -> assert false
             | [xs_values] -> mk_ite_and xs_values xs_ty_named
             | xs_values :: l ->
               asprintf "(or %s %a)"
                 (mk_ite_and xs_values xs_ty_named)
                 (Printer.pp_list_space pp_or_list) l
           in

           let rec reps_aux reps =
             match reps with
             | [] -> asprintf "%a" pp_dummy_value_of_type ty
             | [srep,xs_values_list] ->
               if Options.get_interpretation_use_underscore () then
                 asprintf "(ite %s %s %s)"
                   (mk_ite_or xs_values_list)
                   srep
                   (reps_aux [])
               else
                 srep
             | (srep,xs_values_list) :: l ->
               asprintf "(ite %s %s %s)"
                 (mk_ite_or xs_values_list)
                 srep
                 (reps_aux l)
           in
           if List.length representants = 1 then
             sprintf "%s" (fst (List.hd representants))
           else
             reps_aux representants
         in
         print_fun_def fmt f xs_ty_named ty rep;
      ) fprofs;
    !records

  let output_arrays_counterexample fmt _arrays =
    Printer.print_fmt fmt "@ ; Arrays not yet supported@ "

end
(* of module SmtlibCounterExample *)

module Why3CounterExample = struct

  let output_constraints fmt prop_model =
    let assertions = SE.fold (fun e acc ->
        (asprintf "%s(assert %a)@ " acc SmtlibCounterExample.pp_term e)
      ) prop_model "" in
    Printer.print_fmt ~flushed:false fmt "@ ; constants@ ";
    MS.iter (fun _ (name,ty,args_ty) ->
        match args_ty with
        | [] ->
          Printer.print_fmt ~flushed:false fmt "(declare-const %s %s)@ "
            name ty
        | l ->
          Printer.print_fmt ~flushed:false fmt "(declare-fun %s (%s) %s)@ "
            name
            (String.concat " " l)
            ty
      ) !constraints;
    Printer.print_fmt ~flushed:false fmt "@ ; assertions@ ";
    Printer.print_fmt fmt ~flushed:false "%s" assertions

end
(* of module Why3CounterExample *)

let output_concrete_model fmt props ~functions ~constants ~arrays =
  if get_interpretation () then begin
    Printer.print_fmt ~flushed:false fmt "@[<v 0>unknown@ ";
    Printer.print_fmt ~flushed:false fmt "@[<v 2>(model@,";
    if Options.get_model_type_constraints () then begin
      Why3CounterExample.output_constraints fmt props
    end;

    Printer.print_fmt fmt "@ ; Functions@ ";
    let records = SmtlibCounterExample.output_functions_counterexample
        fmt  MS.empty functions in

    Printer.print_fmt fmt "@ ; Constants@ ";
    SmtlibCounterExample.output_constants_counterexample
      fmt records constants;

    SmtlibCounterExample.output_arrays_counterexample fmt arrays;

    Printer.print_fmt fmt "@]@ )";
  end;
