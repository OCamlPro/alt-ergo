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

let get_type s =
  try let (_, t) = Sorts.find s !h in Some t
  with Not_found -> None

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

let debug = false

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
        let s = Str.regexp_string destr in
        try let _ = Str.search_forward s d 0 in
          Some rep
        with Not_found ->
          find_destrs destr destrs
    in

    let print_destr fmt (destrs,lbs) =
      List.iter (fun (destr, _ty_destr) ->
          let destr = Hstring.view destr in
          match find_destrs destr destrs with
          | None -> fprintf fmt "<missing value for %s> " destr
          | Some rep -> fprintf fmt "%s " rep
        ) (List.rev lbs)
    in
    match Records.find_opt (Hstring.view n) !records with
    | None -> assert false
    | Some [] -> assert false
    | Some destrs ->
      asprintf "%s %a"
        (Hstring.view cstr)
        print_destr (destrs,lbs)

  let x_print fmt (_ , ppr) = fprintf fmt "%s" ppr

  let x_print_why3 fmt (_ , ppr) =
    fprintf fmt "%s"
      (match ppr with
       | "True" -> "true"
       | "False" -> "false"
       | _ -> ppr)

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

  let pp_type fmt t =
    let open Ty in
    (*     let print_destr fmt (destr, ty) =
           fprintf fmt "(%s:%a) " (Hstring.view destr) print ty
           in *)
    Format.fprintf fmt "%s" (match t with
        | Tint -> "Int"
        | Treal -> "Real"
        | Tbool -> "Bool"
        | Text (_, t) -> Hstring.view t
        | Trecord { args = lv; name = n; _ } ->
          (*           asprintf "(args:%a) %s (constr:%s) (destr:%a)"
                       print_list lv
                       (Hstring.view n)
                       (Hstring.view cstr)
                       (Printer.pp_list_no_space print_destr) lbs *)
          asprintf "%a %s"
            print_list lv
            (Hstring.view n)
        | _ -> asprintf "%a" print t
      )

  let get_qtmk f qtmks =
    try Sorts.find f qtmks
    with Not_found -> f

  let output_constants_counterexample fmt cprofs fprofs =
    (* Sorts.iter (fun f (nbargs, t) ->
     *     Format.eprintf "Sort: %s(%d): %s@." f nbargs t) !h; *)
    Printer.print_fmt ~flushed:false (get_fmt_mdl()) "@[<v 0>(model@,";
    let qtmks = Profile.fold
        (fun (f, xs_ty, ty) st acc ->
           if debug then
             Printer.print_dbg "f:%a / xs_ty:%a / ty:%a"
               Sy.print f
               (Printer.pp_list_no_space Ty.print) xs_ty
               Ty.print ty;

           Profile.V.fold
             (fun (xs, rep) acc ->


                let print_xs fmt (e,(r,xs)) =
                  fprintf fmt "(%a / %a / %s), " E.print e X.print r xs
                in
                let print_rep fmt (r,rep) =
                  fprintf fmt "(%a %s) " X.print r rep
                in

                if debug then
                  Printer.print_dbg ~header:false "xs:%a / rep:%a"
                    (Printer.pp_list_no_space print_xs) xs
                    print_rep rep;
                let s = asprintf "%a" (print_symb ty) f in
                let rep = asprintf "%a" x_print rep in

                begin match xs_ty with
                  | [Ty.Trecord r] ->
                    add_records_destr
                      (Hstring.view r.name)
                      (Sy.to_string f)
                      rep
                  | _ -> ()
                end;

                match get_type s, get_type rep with
                | Some ts, Some tr when String.equal ts tr ->
                  (*    Printer.print_dbg "s: %s(%s) / rep: %s (%s)"
                        s ts rep tr; *)
                  if debug then Printer.print_dbg "s:%s(:%s) / rep:%s(:%s)"
                      s ts rep tr;
                  Sorts.add
                    rep (Format.asprintf "(%s %a)" s print_args xs)
                    acc
                | Some ts, Some tr ->
                  if debug then Printer.print_dbg "s:%s(:%s) / rep:%s(:%s)"
                      s ts rep tr;
                  acc;
                | Some ts, None ->
                  if debug then Printer.print_dbg "s:%s(:%s) / rep:%s(:_)"
                      s ts rep;
                  acc;
                | None, Some tr ->
                  if debug then Printer.print_dbg "s:%s(:_) / rep:%s(:%s)"
                      s rep tr;
                  acc;
                | None, None ->
                  if debug then Printer.print_dbg "s:%s(:_) / rep:%s(:_)"
                      s rep;
                  acc;
             ) st acc;
        ) fprofs Sorts.empty in
    if debug then
      Printer.print_dbg "CPROFS";
    Profile.iter
      (fun (f, xs_ty, ty) st ->
         match Profile.V.elements st with
         | [[], rep] ->
           let rep = Format.asprintf "%a" x_print_why3 rep in
           if debug then
             Printer.print_dbg ~header:false "rep:%s / lsit lenght %d"
               rep (List.length xs_ty);

           let qtmks =
             match ty with
             | Ty.Trecord r ->
               let constr = mk_records_constr r in
               let sconstr = sprintf "(%s)" constr in
               Sorts.add rep sconstr qtmks
             | _ -> qtmks
           in

           Printer.print_fmt ~flushed:false fmt
             "(define-fun %a () %a %s)@ "
             (print_symb ty) f pp_type ty (get_qtmk rep qtmks)
         | _ -> assert false
      ) cprofs

end
(* of module SmtlibCounterExample *)

module Why3CounterExample = struct
  let output_constraints fmt constraints =
    let print_constraints fmt _constraint =
      (* TODO *)
      fprintf fmt ""
    in
    Printer.print_fmt fmt ";; Constraints@ %a"
      (Printer.pp_list_no_space print_constraints) constraints
end
(* of module Why3CounterExample *)

let output_concrete_model fmt functions constants arrays =
  if get_interpretation () then
    if
      Options.get_output_format () == Why3 ||
      Options.get_output_format () == Smtlib2 ||
      (Options.get_why3_counterexample ()) then begin

      if Options.get_output_format () == Why3 ||
         (Options.get_why3_counterexample ()) then begin
        (* TODO : add a printer to output constraint with assertions *)
        Why3CounterExample.output_constraints fmt []
      end;

      Printer.print_fmt ~flushed:false fmt "@[<v 0>unknown@ ";
      SmtlibCounterExample.output_constants_counterexample fmt
        constants functions;

      Printer.print_fmt fmt "@])";
    end
    else if Options.get_output_format () == Native then begin
      Printer.print_fmt ~flushed:false fmt "@[<v 2>(@ ";
      Printer.print_fmt ~flushed:false fmt "Constants@ ";
      AECounterExample.output_constants_counterexample fmt constants;
      Printer.print_fmt ~flushed:false fmt "Functions@ ";
      AECounterExample.output_functions_counterexample fmt functions;
      Printer.print_fmt ~flushed:false fmt "Arrays@ ";
      AECounterExample.output_arrays_counterexample fmt arrays;
      Printer.print_fmt fmt "@])";
    end
    else
      Printer.print_fmt fmt "Output format not recognised"