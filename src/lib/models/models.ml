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

let assert_has_depth_one (e, _) =
  match X.term_extract e with
  | Some t, true -> assert (E.depth t = 1);
  | _ -> ()

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
                List.iter (fun (_,x) -> assert_has_depth_one x) xs;
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
                  List.iter (fun (_,x) -> assert_has_depth_one x) xs;
               )st;
             Printer.print_fmt ~flushed:false fmt "@]@ ";
           | _ -> assert false

        ) arrays;
      Printer.print_fmt fmt "@]";
    end

end
(* of module AECounterExample *)

module SmtlibCounterExample = struct

  module Records = Map.Make(String)
  let records = ref Records.empty

  let add_records_destr record destr rep =
    match Records.find_opt record !records with
    | None ->
      records := Records.add record [(destr,rep)] !records
    | Some destrs ->
      records := Records.add record ((destr,rep) :: destrs) !records

  let mk_records_constr
      { Ty.name = n; record_constr = cstr; lbs = lbs; _} =
    let rec find_destrs destr destrs =
      match destrs with
      | [] -> None
      | (d,rep) :: destrs ->
        if String.equal d destr then Some rep
        else find_destrs destr destrs
    in

    let print_destr fmt (destrs,lbs) =
      List.iter (fun (destr, _ty_destr) ->
          let destr = Hstring.view destr in
          match find_destrs destr destrs with
          | None -> fprintf fmt "<missing value for %s> " destr
          | Some rep -> fprintf fmt "%s " rep
        ) lbs
    in
    match Records.find_opt (Hstring.view n) !records with
    | None -> assert false
    | Some [] -> assert false
    | Some destrs ->
      asprintf "%s %a"
        (Hstring.view cstr)
        print_destr (destrs,lbs)

  let x_print fmt (_ , ppr) = fprintf fmt "%s" ppr

  let to_string_type t =
    asprintf "%a" Ty.print t

  let pp_term fmt t =
    match E.symbol_info t with
    | Sy.Name (n,_) -> begin
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
    | _ -> E.print fmt t

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
               let constr = mk_records_constr r in
               sprintf "(%s)" constr
             | _ -> rep
           in

           print_fun_def fmt f [] ty rep
         | _ -> assert false
      ) cprofs

  let check_is_destr ty f rep =
    match ty with
    | [Ty.Trecord r] ->
      add_records_destr
        (Hstring.view r.name)
        (Sy.to_string f)
        rep
    | _ -> ()

  let output_functions_counterexample fmt fprofs =
    Profile.iter
      (fun (f, xs_ty, ty) st ->
         let xs_ty_named = List.mapi (fun i ty ->
             ty,(sprintf "arg_%d" i)
           ) xs_ty in

         let rep =
           let representants =
             Profile.V.fold (fun (xs_values,(rep,srep)) acc ->
                 assert ((List.length xs_ty_named) = (List.length xs_values));
                 check_is_destr xs_ty f srep;
                 (xs_values,rep) :: acc
               ) st [] in

           let rec reps_aux reps =
             match reps with
             | [] -> assert false
             | [_xs_values,rep] ->
               asprintf "%a" X.print rep
             | (xs_values,rep) :: l ->
               let rec mk_ite_cond xs tys =
                 match xs, tys with
                 | [],[] -> assert false
                 | [xs,_],[_ty,name] ->
                   asprintf "(= %s %a)" name Expr.print xs
                 | (xs,_) :: l1, (_ty,name) :: l2 ->
                   asprintf "(and (= %s %a) %s)"
                     name
                     Expr.print xs
                     (mk_ite_cond l1 l2)
                 | _, _ -> assert false
               in
               asprintf "(ite %s %a %s)"
                 (mk_ite_cond xs_values xs_ty_named)
                 X.print rep
                 (reps_aux l)
           in
           reps_aux representants
         in
         print_fun_def fmt f xs_ty_named ty rep;
      ) fprofs

end
(* of module SmtlibCounterExample *)

module Why3CounterExample = struct

  let output_constraints fmt prop_model =
    let assertions = SE.fold (fun e acc ->
        (asprintf "%s(assert %a)@ " acc SmtlibCounterExample.pp_term e)
      ) prop_model "" in
    Sorts.iter (fun _ (name,ty) ->
        Printer.print_fmt ~flushed:false fmt "(declare-const %s %s)@ " name ty
      ) !constraints;
    Printer.print_fmt fmt "%s" assertions

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
