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

module Sorts = Map.Make(String)

let h = ref Sorts.empty

let sorts parsed =
  let open Parsed in
  Format.eprintf "@[<v 2>";
  Seq.iter (fun d -> match d with
      | Parsed.Axiom (_, _, _, le) -> begin
          match le.pp_desc with
          | PPapp("sort", f)
          | PPforall_named (_, _, _, {pp_desc = PPapp("sort", f); _}) ->
            begin
              match f with
              | [{pp_desc = PPapp(t, _); _}; {pp_desc = PPapp(f, args); _}] ->
                h := Sorts.add f (List.length args, t) !h
              | _ -> ()
            end
          | _ -> ()
        end
      | _ -> ()
    ) parsed

module Profile = struct

  module P = Map.Make
      (struct
        type t = Sy.t * Ty.t list * Ty.t

        let (|||) c1 c2 = if c1 <> 0 then c1 else c2

        let compare (a1, b1, c1)  (a2, b2, c2) =
          let l1_l2 = List.length b1 - List.length b2 in
          let c = l1_l2 ||| (Ty.compare c1 c2) ||| (Sy.compare a1 a2) in
          if c <> 0 then c
          else
            let c = ref 0 in
            try
              List.iter2
                (fun ty1 ty2 ->
                   let d = Ty.compare ty1 ty2 in
                   if d <> 0 then begin c := d; raise Exit end
                ) b1 b2;
              0
            with
            | Exit -> assert (!c <> 0); !c
            | Invalid_argument _ -> assert false
      end)

  module V = Set.Make
      (struct
        type t = (E.t * (X.r * string)) list * (X.r * string)
        let compare (l1, (v1,_)) (l2, (v2,_)) =
          let c = X.hash_cmp v1 v2 in
          if c <> 0 then c
          else
            let c = ref 0 in
            try
              List.iter2
                (fun (_,(x,_)) (_,(y,_)) ->
                   let d = X.hash_cmp x y in
                   if d <> 0 then begin c := d; raise Exit end
                ) l1 l2;
              !c
            with
            | Exit -> !c
            | Invalid_argument _ -> List.length l1 - List.length l2
      end)

  let add p v mp =
    let prof_p = try P.find p mp with Not_found -> V.empty in
    if V.mem v prof_p then mp
    else P.add p (V.add v prof_p) mp

  let iter = P.iter

  let fold = P.fold

  let empty = P.empty

  let is_empty = P.is_empty
end

let constraints = ref Sorts.empty

let assert_has_depth_one_at_most (e, _) =
  match X.term_extract e with
  | Some t, true ->
    assert (E.depth t <= 1); (* true and false have depth = -1 *)
  | _ ->
    ()

module AECounterExample = struct

  let x_print fmt (_ , ppr) = fprintf fmt "%s" ppr

  let print_args fmt l =
    match l with
    | [] -> assert false
    | [_,e] ->
      fprintf fmt "%a" x_print e;
    | (_,e) :: l ->
      fprintf fmt "%a" x_print e;
      List.iter (fun (_, e) -> fprintf fmt " %a" x_print e) l

  let print_symb ty fmt f =
    match f, ty with
    | Sy.Op Sy.Record, Ty.Trecord { Ty.name ; _ } ->
      fprintf fmt "%a__%s" Sy.print f (Hstring.view name)

    | _ -> Sy.print fmt f

  let output_constants_counterexample fmt cprofs =
    (*printf "; constants:@.";*)
    Profile.iter
      (fun (f, _xs_ty, ty) st ->
         match Profile.V.elements st with
         | [[], rep] ->
           (*printf "  (%a %a)  ; %a@."
             (print_symb ty) f x_print rep Ty.print ty*)
           Printer.print_fmt ~flushed:false fmt
             "(s(%d): %a, rep: %a)@ "
             (List.length _xs_ty) (print_symb ty) f x_print rep
         | _ -> assert false
      ) cprofs

  let output_functions_counterexample fmt fprofs =
    if not (Profile.is_empty fprofs) then begin
      Printer.print_fmt ~flushed:false fmt "@[<v 2>@ ";
      (*printf "@.; functions:@.";*)
      Profile.iter
        (fun (f, _xs_ty, ty) st ->
           (*printf "  ; fun %a : %a -> %a@."
             (print_symb ty) f Ty.print_list xs_ty Ty.print ty;*)
           Printer.print_fmt ~flushed:false fmt "@[<v 2>@ ";
           Profile.V.iter
             (fun (xs, rep) ->
                Printer.print_fmt ~flushed:false fmt
                  "((s: %a, args: %a) rep: %a)@ "
                  (print_symb ty) f print_args xs x_print rep;
                List.iter (fun (_,x) -> assert_has_depth_one_at_most x) xs;
             )st;
           Printer.print_fmt ~flushed:false fmt "@]@ ";
        ) fprofs;
      Printer.print_fmt fmt "@]";
    end

  let output_arrays_counterexample fmt arrays =
    if not (Profile.is_empty arrays) then begin
      Printer.print_fmt ~flushed:false fmt "@[<v 2>@ ";
      (*printf "; arrays:@.";*)
      Profile.iter
        (fun (f, xs_ty, ty) st ->
           match xs_ty with
             [_] ->
             (*printf "  ; array %a : %a -> %a@."
               (print_symb ty) f Ty.print tyi Ty.print ty;*)
             Printer.print_fmt ~flushed:false fmt "@[<v 2>@ ";
             Profile.V.iter
               (fun (xs, rep) ->
                  Printer.print_fmt ~flushed:false fmt
                    "((%a %a) %a)@ "
                    (print_symb ty) f print_args xs x_print rep;
                  List.iter (fun (_,x) -> assert_has_depth_one_at_most x) xs;
               )st;
             Printer.print_fmt ~flushed:false fmt "@]@ ";
           | _ -> assert false

        ) arrays;
      Printer.print_fmt fmt "@]";
    end

end
(* of module AECounterExample *)

module Pp_smtlib_term = struct

  let to_string_type t =
    asprintf "%a" Ty.print t

  let rec print fmt t =
    let f,xs,ty = E.get_infos t in
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

    | Sy.Name (n,_), _ -> begin
        try
          let constraint_name,_ty_name =
            Sorts.find (Hstring.view n) !constraints in
          fprintf fmt "%s" constraint_name
        with _ ->
          let constraint_name = "c_"^(Hstring.view n)  in
          constraints := Sorts.add (Hstring.view n)
              (constraint_name,to_string_type (E.type_info t)) !constraints;
          fprintf fmt "%s" constraint_name
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
    | _ -> asprintf "%a" pp_term (Expr.fresh_name ty)

  let pp_dummy_value_of_type fmt ty =
    if not (Options.get_interpretation_use_underscore ()) then
      let d = dummy_value_of_type ty in
      fprintf fmt "%s " d
    else
      fprintf fmt "_ "

  module Records = Map.Make(String)
  module Destructors = Map.Make(String)
  let records = ref Records.empty

  let add_records_destr record_name destr_name rep =
    let destrs =
      try Records.find record_name !records
      with Not_found -> Destructors.empty
    in
    let destrs =
      Destructors.add destr_name rep destrs in
    records := Records.add record_name destrs !records

  let mk_records_constr record_name
      { Ty.name = _n; record_constr = cstr; lbs = lbs; _} =
    let find_destrs destr destrs =
      try let rep = Destructors.find destr destrs in
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
      try Records.find (Sy.to_string record_name) !records
      with Not_found -> Destructors.empty
    in
    asprintf "%s %a"
      (Hstring.view cstr)
      print_destr (destrs,lbs)

  let add_record_constr record_name
      { Ty.name = _n; record_constr = _cstr; lbs = lbs; _} xs_values =
    List.iter2 (fun (destr,_) (rep,_) ->
        add_records_destr
          record_name
          (Hstring.view destr)
          (asprintf "%a" pp_term rep)
      ) lbs xs_values

  let check_records xs_ty_named xs_values f ty rep =
    match xs_ty_named with
    | [Ty.Trecord _r, _arg] -> begin
        match xs_values with
        | [record_name,_] ->
          add_records_destr
            (asprintf "%a" Expr.print record_name)
            (Sy.to_string f)
            rep
        | [] | _ -> ()
      end
    | _ ->
      match ty with
      | Ty.Trecord r ->
        add_record_constr rep r xs_values
      | _ -> ()

  let print_fun_def fmt name args ty t =
    let print_args fmt (ty,name) =
      Format.fprintf fmt "(%s %a)" name Ty.print ty in
    let defined_value =
      try
        fst (Sorts.find (Sy.to_string name) !constraints)
      with _ -> t
    in

    Printer.print_fmt ~flushed:false fmt
      "(define-fun %a (%a) %a %s)@ "
      Sy.print name
      (Printer.pp_list_space (print_args)) args
      Ty.print ty
      defined_value

  let output_constants_counterexample fmt cprofs =
    Profile.iter
      (fun (f, xs_ty, ty) st ->
         assert (xs_ty == []);
         match Profile.V.elements st with
         | [[], rep] ->
           let rep = Format.asprintf "%a" x_print rep in
           let rep =
             match ty with
             | Ty.Trecord r ->
               let constr = mk_records_constr f r in
               sprintf "(%s)" constr
             | _ -> rep
           in

           print_fun_def fmt f [] ty rep
         | _ -> assert false
      ) cprofs

  module Rep = Map.Make(String)

  let output_functions_counterexample fmt fprofs =
    Profile.iter
      (fun (f, xs_ty, ty) st ->
         let xs_ty_named = List.mapi (fun i ty ->
             ty,(sprintf "arg_%d" i)
           ) xs_ty in

         let rep =
           let representants =
             Profile.V.fold (fun (xs_values,(_rep,srep)) acc ->
                 assert ((List.length xs_ty_named) = (List.length xs_values));
                 check_records xs_ty_named xs_values f ty srep;
                 let reps = try Rep.find srep acc with Not_found -> [] in
                 Rep.add srep (xs_values :: reps) acc
               ) st Rep.empty in

           let representants = Rep.fold (fun srep xs_values_list acc ->
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
      ) fprofs

  let output_arrays_counterexample fmt _arrays =
    fprintf fmt "@ ; Arrays not yet supported@ "

end
(* of module SmtlibCounterExample *)

module Why3CounterExample = struct

  let output_constraints fmt prop_model =
    let assertions = SE.fold (fun e acc ->
        (asprintf "%s(assert %a)@ " acc SmtlibCounterExample.pp_term e)
      ) prop_model "" in
    Printer.print_fmt ~flushed:false fmt "@ ; constants@ ";
    Sorts.iter (fun _ (name,ty) ->
        Printer.print_fmt ~flushed:false fmt "(declare-const %s %s)@ " name ty
      ) !constraints;
    Printer.print_fmt ~flushed:false fmt "@ ; assertions@ ";
    Printer.print_fmt fmt ~flushed:false "%s" assertions

end
(* of module Why3CounterExample *)

let output_concrete_model fmt props functions constants arrays =
  if get_interpretation () then
    if
      Options.get_output_format () == Why3 ||
      Options.get_output_format () == Smtlib2 then begin

      Printer.print_fmt ~flushed:false fmt "@[<v 0>unknown@ ";
      Printer.print_fmt ~flushed:false fmt "@[<v 2>(model@,";
      if Options.get_output_format () == Why3 then begin
        Why3CounterExample.output_constraints fmt props
      end;

      fprintf fmt "@ ; Functions@ ";
      SmtlibCounterExample.output_functions_counterexample fmt functions;
      fprintf fmt "@ ; Constants@ ";
      SmtlibCounterExample.output_constants_counterexample fmt constants;

      SmtlibCounterExample.output_arrays_counterexample fmt arrays;

      Printer.print_fmt fmt "@]@ )";
    end
    else if Options.get_output_format () == Native then begin
      Printer.print_fmt ~flushed:false fmt "@[<v 2>(@ ";
      Printer.print_fmt ~flushed:false fmt "Constants@ ";
      AECounterExample.output_constants_counterexample fmt constants;
      Printer.print_fmt ~flushed:false fmt "@ Functions@ ";
      AECounterExample.output_functions_counterexample fmt functions;
      Printer.print_fmt ~flushed:false fmt "@ Arrays@ ";
      AECounterExample.output_arrays_counterexample fmt arrays;
      Printer.print_fmt fmt "@])";
    end
    else
      Printer.print_fmt fmt "Output format not recognised"
