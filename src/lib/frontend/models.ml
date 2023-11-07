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

type objective_value =
  | Obj_pinfty
  | Obj_minfty
  | Obj_val of string
  | Obj_unk

type t = {
  propositional : Expr.Set.t;
  constants : ModelMap.t;
  functions : ModelMap.t;
  arrays : ModelMap.t;
  objectives: (Expr.t * objective_value) Util.MI.t;
  terms_values : (Shostak.Combine.r * string) Expr.Map.t
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

    | Sy.Name (n, _, _), l -> begin
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

module SmtlibCounterExample = struct
  let fresh_counter = ref 0

  let reset_counter () = fresh_counter := 0

  let pp_term fmt t =
    if Options.get_output_format () == Why3 then
      Pp_smtlib_term.print fmt t
    else
      E.print fmt t

  let pp_abstract_value_of_type ppf ty =
    if not @@ Options.get_interpretation_use_underscore () then begin
      Fmt.pf ppf "(as @@a%i %a)" !fresh_counter Ty.pp_smtlib ty;
      incr fresh_counter
    end
    else
      Fmt.pf ppf "_ "

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
          let destr = Hstring.view destr in
          match find_destrs destr destrs with
          | None ->
            pp_abstract_value_of_type fmt ty_destr
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
      { Ty.name = _n; record_constr = _cstr; lbs = lbs; _} xs_values =
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
      Format.fprintf fmt "(%s %a)" name Ty.pp_smtlib ty in
    let defined_value =
      try
        let res,_,_ = (MS.find (Sy.to_string name) !constraints) in
        dprintf "%s" res
      with _ -> t
    in

    Format.fprintf fmt
      "@ (@[define-fun %a (%a) %a@ %t)@]"
      Sy.print name
      (Printer.pp_list_space (print_args)) args
      Ty.pp_smtlib ty
      defined_value

  let output_constants_counterexample pp fmt records =
    ModelMap.iter
      (fun (f, xs_ty, ty) st ->
         assert (xs_ty == []);
         match ModelMap.V.elements st with
         | [[], rep] ->
           let rep =
             match ty with
             | Ty.Trecord r ->
               let constr = mk_records_constr records f r in
               dprintf "(%s)" constr
             | _ -> dprintf "%a" pp rep
           in

           print_fun_def fmt f [] ty rep
         | _ -> assert false)

  let output_functions_counterexample pp fmt records fprofs =
    let  records = ref records in
    ModelMap.iter
      (fun (f, xs_ty, ty) st ->
         let xs_ty_named = List.mapi (fun i ty ->
             ty,(sprintf "arg_%d" i)
           ) xs_ty in

         let rep =
           let representants =
             ModelMap.V.fold (fun (xs_values,(rep,srep)) acc ->
                 assert ((List.length xs_ty_named) = (List.length xs_values));
                 records :=
                   check_records !records xs_ty_named xs_values f ty srep;
                 let reps = try MX.find rep acc |> snd with Not_found -> [] in
                 MX.add rep (srep, xs_values :: reps) acc
               ) st MX.empty in

           let representants = MX.fold (fun rep (srep, xs_values_list) acc ->
               ((rep, srep),xs_values_list) :: acc) representants [] in

           let rec mk_ite_and xs tys =
             match xs, tys with
             | [],[] -> assert false
             | [_,rs],[_ty,name] ->
               dprintf "(= %s %a)" name pp rs
             | (_,rs) :: l1, (_ty,name) :: l2 ->
               dprintf "(and (= %s %a) %t)"
                 name
                 pp rs
                 (mk_ite_and l1 l2)
             | _, _ -> assert false
           in

           let mk_ite_or l =
             let pp_or_list fmt xs_values =
               fprintf fmt "%t" (mk_ite_and xs_values xs_ty_named)
             in
             match l with
             | [] -> assert false
             | [xs_values] -> mk_ite_and xs_values xs_ty_named
             | xs_values :: l ->
               dprintf "(or %t %a)"
                 (mk_ite_and xs_values xs_ty_named)
                 (Printer.pp_list_space pp_or_list) l
           in

           let rec reps_aux reps =
             match reps with
             | [] -> dprintf "%a" pp_abstract_value_of_type ty
             | [srep,xs_values_list] ->
               if Options.get_interpretation_use_underscore () then
                 dprintf "(@[<hv>ite %t@ %a@ %t)@]"
                   (mk_ite_or xs_values_list)
                   pp srep
                   (reps_aux [])
               else
                 dprintf "%a" pp srep
             | (srep,xs_values_list) :: l ->
               dprintf "(@[<hv>ite %t@ %a@ %t)@]"
                 (mk_ite_or xs_values_list)
                 pp srep
                 (reps_aux l)
           in
           if List.length representants = 1 then
             dprintf "%a" pp (fst (List.hd representants))
           else
             reps_aux representants
         in
         (* Only print declared (but not defined!) function symbols -- note
            that we still need to *handle* other symbols without printing them
            because they could be record accessors that must be added to the
            `records` reference *)
         match f with
         | Sy.Name (_, _, false) -> print_fun_def fmt f xs_ty_named ty rep
         | _ -> ()
      ) fprofs;
    !records

  let output_objectives fmt objectives =
    (* TODO: we can decide to print objectives to stderr if
       Options.get_objectives_in_interpretation() is enabled *)
    if not (Options.get_objectives_in_interpretation()) &&
       not (Util.MI.is_empty objectives)
    then begin
      Format.fprintf fmt "@[<v 3>(objectives";
      Util.MI.iter
        (fun _i (e, x) ->
           Format.fprintf fmt "@ (%a %a)"
             E.print e
             (fun fmt () ->
                match x with
                | Obj_pinfty -> Format.fprintf fmt "+oo"
                | Obj_minfty -> Format.fprintf fmt "-oo"
                | Obj_val s -> Format.fprintf fmt "%s" s
                | Obj_unk -> Format.fprintf fmt "(interval -oo +oo)"
             ) ()
        )objectives;
      Printer.print_fmt fmt "@]@ )"
    end

end
(* of module SmtlibCounterExample *)

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

end
(* of module Why3CounterExample *)

(* The [value_defn] type is a mini-language of the expressions that can occur in
   constant values. *)
type value_defn =
  | Store of value_defn * value_defn * value_defn
  (* An array store: [(store array key value)] *)
  | Constant of Symbols.t * Ty.t
  (* A constant of a given type. If the constant is defined in a model, it
     must be resolved before being printed. *)
  | Value of X.r * string
  (* A leaf semantic value. This must be an actual value, i.e. it must not
     contain any uninterpreted terms. *)
  | Abstract of string
  (* An unique abstract value *)

let value (r, s) =
  match X.term_extract r with
  | Some t, _ ->
    begin match E.term_view t with
      | { f = Name _ as sy; _ } -> Constant (sy, X.type_info r)
      | _ -> Value (r, s)
    end
  | _ ->
    Value (r, s)

let rec pp_value ppk ppf = function
  | Store (a, k, v) ->
    Format.fprintf ppf "(@[<hv>store@ %a@ %a %a)@]"
      (pp_value ppk) a
      (pp_value ppk) k
      (pp_value ppk) v
  | Constant (sy, t) -> ppk ppf (sy, t)
  | Value (_, s) -> Format.pp_print_string ppf s
  | Abstract s -> Format.pp_print_string ppf s

let pp_constant ppf (_sy, t) =
  Fmt.pf ppf "%a" SmtlibCounterExample.pp_abstract_value_of_type t

let output_concrete_model fmt m =
  SmtlibCounterExample.reset_counter ();
  if ModelMap.(is_suspicious m.functions || is_suspicious m.constants
               || is_suspicious m.arrays) then
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

  Printer.print_fmt fmt "@]@,)";
  SmtlibCounterExample.output_objectives fmt m.objectives
