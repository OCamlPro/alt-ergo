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
let used_names = ref Util.SS.empty
let used_fresh = ref Util.MS.empty

type objective_value =
  | Obj_pinfty
  | Obj_minfty
  | Obj_val of string
  | Obj_unk

type t = {
  propositional : Expr.Set.t;
  constants : ModelMap.V.t ModelMap.P.t;
  functions : ModelMap.V.t ModelMap.P.t;
  arrays : ModelMap.V.t ModelMap.P.t;
  objectives : (Expr.t * objective_value) Util.MI.t;
  terms_values : (X.r * string) ME.t (* a map from terms to their values
                                        in the model (as a
                                        representative of type X.r and
                                        as a string *)
}

module Pp_smtlib_term = struct

  let to_string_type t =
    asprintf "%a" Ty.print t

  let cpt = ref 0
  let check_used_logics name =
    let rec aux s acc =
      if Util.SS.mem s !used_names then begin
        try Util.MS.find s acc
        with Not_found ->
          incr cpt;
          let res = sprintf "%s_%d" s !cpt in
          let acc = Util.MS.add s res acc in
          aux s acc
      end
      else s
    in
    aux name !used_fresh

  let fresh_arg i =
    check_used_logics (sprintf "arg_%d" i)

  let cpt_fresh_type_value = ref 0
  let fresh_type_value ty =
    incr cpt_fresh_type_value;
    check_used_logics
      (sprintf "val_%s_%d"
         (to_string_type ty)
         !cpt_fresh_type_value)

  let check_fresh s =
    if Hstring.is_fresh_skolem s || Hstring.is_fresh_string s then
      check_used_logics (sprintf "ae_%s" s)
    else
      s

  let hstring_view h =
    let s = Hstring.view h in
    check_fresh s

  let print_hstring fmt h =
    fprintf fmt "%s" (hstring_view h)

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
          else fprintf fmt "(%a >= %a)" print a print b

        | Sy.L_neg_pred, [a] ->
          fprintf fmt "(not %a)" print a

        | Sy.L_built (Sy.IsConstr hs), [e] ->
          if get_output_smtlib () then
            fprintf fmt "((_ is %a) %a)" print_hstring hs print e
          else
            fprintf fmt "(%a ? %a)" print e print_hstring hs

        | Sy.L_neg_built (Sy.IsConstr hs), [e] ->
          if get_output_smtlib () then
            fprintf fmt "(not ((_ is %a) %a))" print_hstring hs print e
          else
            fprintf fmt "not (%a ? %a)" print e print_hstring hs

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

    | Sy.Op (Sy.Extract (i, j)), [e] ->
      fprintf fmt "%a^{%d,%d}" print e i j

    | Sy.Op (Sy.Access field), [e] ->
      if get_output_smtlib () then
        fprintf fmt "(%a %a)" print_hstring field print e
      else
        fprintf fmt "%a.%a" print e print_hstring field

    | Sy.Op (Sy.Record), _ ->
      begin match ty with
        | Ty.Trecord { Ty.lbs = lbs; _ } ->
          assert (List.length xs = List.length lbs);
          fprintf fmt "{";
          ignore (List.fold_left2 (fun first (field,_) e ->
              fprintf fmt "%s%a = %a"  (if first then "" else "; ")
                print_hstring field print e;
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
      fprintf fmt "%a(%a)" print_hstring hs print_list l

    | Sy.Op _, [e1; e2] ->
      if get_output_smtlib () then
        fprintf fmt "(%a %a %a)" Sy.print f print e1 print e2
      else
        fprintf fmt "(%a %a %a)" print e1 Sy.print f print e2

    | Sy.Op Sy.Destruct (hs, grded), [e] ->
      fprintf fmt "%a#%s%a"
        print e (if grded then "" else "!") print_hstring hs


    | Sy.In(lb, rb), [t] ->
      fprintf fmt "(%a in %a, %a)" print t Sy.print_bound lb Sy.print_bound rb

    | Sy.Name (n,_), l ->
      if Options.get_output_format () == Why3 then
        begin
          let constraint_name =
            try let constraint_name,_,_ =
                  (MS.find (hstring_view n) !constraints) in
              constraint_name
            with _ ->
              let constraint_name = "c_"^(hstring_view n)  in
              constraints := MS.add (hstring_view n)
                  (constraint_name,
                   to_string_type (E.type_info t),
                   List.map (fun e -> to_string_type (E.type_info e)) l
                  ) !constraints;
              constraint_name
          in
          match l with
          | [] -> fprintf fmt "%s" constraint_name
          | l ->
            fprintf fmt "(%s %a)"
              constraint_name (Printer.pp_list_space print) l;
        end
      else
        fprintf fmt "%a" print_hstring n

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
    | _ -> Pp_smtlib_term.fresh_type_value ty

  let pp_dummy_value_of_type fmt ty =
    if not (Options.get_interpretation_use_underscore ()) then
      let d = dummy_value_of_type ty in
      fprintf fmt "%s " d
    else
      fprintf fmt "_ "

  let pp_value_of_type fmt (v,ty) =
    if Hstring.is_fresh_skolem v || Hstring.is_fresh_string v then
      pp_dummy_value_of_type fmt ty
    else
      fprintf fmt "%s" v

  let add_records_destr records record_name destr_name rep =
    let destrs =
      try MS.find record_name records
      with Not_found -> MS.empty
    in
    let destrs =
      MS.add destr_name rep destrs in
    MS.add record_name destrs records

  let mk_records_constr records record_name
      { Ty.name = _n; record_constr = cstr; lbs = lbs; _} =
    let find_destrs destr destrs =
      try let rep = MS.find destr destrs in
        Some rep
      with Not_found -> None
    in

    let print_destr fmt (destrs,lbs) =
      List.iter (fun (destr, ty_destr) ->
          let destr = Pp_smtlib_term.hstring_view destr in
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
    asprintf "%a %a"
      Pp_smtlib_term.print_hstring cstr
      print_destr (destrs,lbs)

  let add_record_constr records record_name
      { Ty.name = _n; record_constr = _cstr; lbs = lbs; _} xs_values =
    List.fold_left2(fun records (destr,_) (rep,_) ->
        add_records_destr
          records
          record_name
          (Pp_smtlib_term.hstring_view destr)
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

  let print_fun_def ~is_array fmt name args ty t =
    let print_args fmt (ty,name) =
      Format.fprintf fmt "(%s %a)" name Ty.print ty in
    let defined_value =
      try
        let res,_,_ = (MS.find (Sy.to_string name) !constraints) in res
      with _ -> asprintf "%a" pp_value_of_type (t,ty)
    in

    Printer.print_fmt ~flushed:false fmt
      "(define-%s %a (%a) %a %s)@ "
      (if is_array then "array" else "fun")
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

           print_fun_def ~is_array:false fmt f [] ty rep
         | _ -> assert false
      ) cprofs

  let output_functions_counterexample ?(is_array=false) fmt records fprofs =
    let  records = ref records in
    ModelMap.iter
      (fun (f, xs_ty, ty) st ->
         let xs_ty_named = List.mapi (fun i ty ->
             ty,Pp_smtlib_term.fresh_arg i
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
             | [_,(_,xs)],[_ty,name] ->
               asprintf "(= %s %s)" name (Pp_smtlib_term.check_fresh xs)
             | (_,(_,xs)) :: l1, (_ty,name) :: l2 ->
               asprintf "(and (= %s %s) %s)"
                 name
                 (Pp_smtlib_term.check_fresh xs)
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
                   (Pp_smtlib_term.check_fresh srep)
                   (reps_aux [])
               else
                 Pp_smtlib_term.check_fresh srep
             | (srep,xs_values_list) :: l ->
               asprintf "(ite %s %s %s)"
                 (mk_ite_or xs_values_list)
                 (Pp_smtlib_term.check_fresh srep)
                 (reps_aux l)
           in
           if List.length representants = 1 then
             sprintf "%s" (fst (List.hd representants))
           else
             reps_aux representants
         in
         print_fun_def ~is_array fmt f xs_ty_named ty rep;
      ) fprofs;
    !records

  let output_arrays_counterexample fmt arrays =
    let _records = output_functions_counterexample
        ~is_array:true fmt  MS.empty arrays in
    ()

  let output_objectives fmt objectives =
    (* TODO: we can decide to print objectives to stderr if
       Options.get_objectives_in_interpretation() is enabled *)
    if not (Options.get_objectives_in_interpretation()) &&
       not (Util.MI.is_empty objectives)
    then begin
      Printer.print_fmt fmt "@[<v 3>(objectives";
      Util.MI.iter
        (fun _i (e, x) ->
           Printer.print_fmt ~flushed:false fmt "@ (%a %a)"
             E.print e
             (fun fmt () ->
                match x with
                | Obj_pinfty -> fprintf fmt "+oo"
                | Obj_minfty -> fprintf fmt "-oo"
                | Obj_val s -> fprintf fmt "%s" s
                | Obj_unk -> fprintf fmt "(interval -oo +oo)"
             ) ()
        )objectives;
      Printer.print_fmt fmt "@]@ )"
    end


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
let output_concrete_model ~used_logics ~pp_prop_model fmt m =
  used_names := used_logics;
  if get_interpretation () then begin
    Printer.print_fmt ~flushed:false fmt "@[<v 2>(model@,";
    if pp_prop_model || Options.get_output_format () == Why3 then begin
      Why3CounterExample.output_constraints fmt m.propositional
    end;

    Printer.print_fmt ~flushed:false fmt "@ ; Functions@ ";
    let records = SmtlibCounterExample.output_functions_counterexample
        ~is_array:false fmt  MS.empty m.functions in

    Printer.print_fmt ~flushed:false fmt "@ ; Constants@ ";
    SmtlibCounterExample.output_constants_counterexample
      fmt records m.constants;

    Printer.print_fmt ~flushed:false fmt "@ ; Arrays content@ ";
    SmtlibCounterExample.output_arrays_counterexample fmt m.arrays;

    Printer.print_fmt fmt "@]@ )";
    SmtlibCounterExample.output_objectives fmt m.objectives;
  end
