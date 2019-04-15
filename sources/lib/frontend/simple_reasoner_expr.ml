(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Typed

type value =
    Bool of bool
  | Num of Num.num

let val_compare t1 t2 =
  match t1,t2 with
    Bool true, Bool false -> 1
  | Bool false, Bool true -> -1
  | Bool _, Bool _ -> 0 (* same value *)
  | Num i, Num j -> Num.int_of_num (Num.sub_num i j)
  | Bool _, Num _ -> 1
  | Num _ , Bool _ -> -1

let pretty_value fmt v =
  match v with
    Bool b ->
    Format.fprintf fmt "%b" b
  | Num n ->
    Format.fprintf fmt "%s" (Num.string_of_num n)

module ValueSet = Set.Make (struct type t = value let compare = val_compare end)
module ValueMap = Set.Make (struct type t = value let compare = val_compare end)

let unary_op_opt (op : 'a -> 'b) (v : 'a option) : 'b option =
  match v with
    None -> None
  | Some v -> Some (op v)

(* Lazy evaluation of arguments is important. *)
let op_opt (op : 'a -> 'a -> 'b) (v1 : 'a option) (v2 : 'a option) : 'b option =
  match v1 with
    Some v1 ->
    unary_op_opt
      (fun v2 -> op v1 v2)
      v2
  | None -> None

module Make
    (Annot : sig type annot val mk : 'a -> ('a, annot) annoted end) =
struct

  let true_desc = TTconst Ttrue
  let false_desc = TTconst Tfalse
  let true_symp = Symbols.True
  let false_symp = Symbols.False
  let true_atom = TAtrue
  let false_atom = TAfalse

  let identity l = l
  type a = Annot.annot

  (** All the following function try to check whether the expression in argument is
      true, false or unknown.
      They respectively return Some true, Some false and None.
      Similarily, functions manipulating values with return an option.
  *)

  let solve_const (c : tconstant) : bool option =
    match c with
      Ttrue ->  Some true
    | Tfalse -> Some false
    | _c -> None (* This should not happen if the formula is well typed *)

  let const_to_value (c : tconstant) : value option =
    match c with
    | Tint i -> (
        try Some (Num (Num.num_of_int @@ int_of_string i)) with _ -> None
      )
    | Treal n -> Some (Num n)

    | Ttrue -> Some (Bool true)
    | Tfalse -> Some (Bool false)
    | _ -> None

  let tt_desc_to_value (desc : a tt_desc) : value option =
    match desc with
      TTconst c -> (const_to_value c)
    | _ -> None (* todo : simplify ? *)

  let value_to_tdesc (real : bool) (v : value) : a tt_desc * Ty.t =
    let desc, ty =
      match v with
        Num n ->
        if real then (Treal n),(Ty.Treal)
        else Tint (Num.string_of_num n),(Ty.Tint)
      | Bool true -> Ttrue, Ty.Tbool
      | Bool false -> Tfalse, Ty.Tbool
    in
    (TTconst desc), ty

  let tform_to_value
      ?(simp : a tform -> a tform = identity) (f : a atform) : value option =
    if Options.simplify_verbose ()
    then
      Format.printf "Valuation of formula %a@."
        Typed.print_formula f;
    match simp f.c with
      TFatom {c = TAtrue;_} ->  Some (Bool true)
    | TFatom {c = TAfalse;_} -> Some (Bool false)
    | _ -> None

  let tterm_to_value
      ?(simp : a atterm -> a atterm = identity) (f : a atterm) : value option =
    match (simp f).c.tt_desc with
      TTconst c ->  const_to_value c
    | _ -> None

  let value_to_tterm (real : bool) (v : value) : a atterm =
    let tt_desc,tt_ty = value_to_tdesc real v in
    Annot.mk {tt_ty; tt_desc}

  let fold_left_stop f acc l =
    let rec __fold acc l =
      match l with
        [] -> acc
      | hd :: tl ->
        let acc, stop = f acc hd in
        if stop then acc else
          __fold acc tl
    in __fold acc l

  (* simp : simplification function
     (t,f) : true and false representation in type a
     op : logical operator
  *)

  let oplogic_oper
      ?(simp : a atform -> a atform = identity)
      ((t,f) : a atform * a atform)
      (op : oplogic)
      (l : a atform list) : a atform list =
    if Options.simplify_verbose ()
    then
      Format.printf "Logic operator %s detected.@."
        (Typed.string_of_op op);
    match op with
      OPand -> (
        if Options.simplify_verbose ()
        then
          Format.printf "AND formula@.";
        let l' =
        List.rev
          (fold_left_stop
             (fun (acc : a atform list) elt ->
                let selt : a atform = simp elt in
                match tform_to_value selt with
                  Some (Bool true) ->
                  if Options.simplify_verbose ()
                  then
                    Format.printf "%a is true, removing it from formula@."
                      Typed.print_formula selt;
                  acc, false
                | Some (Bool false) ->
                  if Options.simplify_verbose ()
                  then
                    Format.printf "%a is false, ending@."
                      Typed.print_formula selt;
                  [f], true
                | _ ->
                  if Options.simplify_verbose ()
                  then
                    Format.printf "%a is unknown@."
                      Typed.print_formula selt;
                  (selt :: acc), false
             )
             []
             l
          )
        in
        if l' = [] then [t]
        else l'
      )
    | OPor ->
      List.rev
        (fold_left_stop
           (fun (acc : a atform list) elt ->
              let selt = simp elt in
              match tform_to_value selt with
                Some (Bool true) -> [t], true
              | Some (Bool false) -> acc, false
              | _ -> (selt :: acc), false
           )
           []
           l
        )

    | OPxor ->
         let exps, xor =
           List.fold_left
             (fun (acc,xor) elt -> (* xor is a boolean extracted from trivial exprs*)
                let selt = simp elt in
                match tform_to_value selt with
                  Some (Bool b) -> acc,(xor <> b)
                | _ -> (selt :: acc), xor
             )
             ([], false)
             l
         in
         if xor
         then f :: List.rev exps
         else t :: List.rev exps

    | OPimp -> l (* No specification on implications with more than 2 elts *)
    | OPnot -> List.map simp l
    | OPiff ->
      let exps, bool_opt =
        fold_left_stop
          (fun (acc,eq) elt : ((a atform list * bool option) * bool) ->
             (* eq is a boolean extracted from trivial exprs*)
             let selt = simp elt in
             match tform_to_value selt, eq with
               Some (Bool b), Some eq' ->
               if b <> eq'
               then ([f], (Some true)), true
               else (acc,eq), false
             | Some (Bool b), _ -> (acc,(Some b)), false
             | _,_ -> ((selt :: acc), eq), false
          )
          ([], None)
          l
      in (
        match bool_opt with
          Some true -> t :: List.rev exps
        | Some false -> f :: List.rev exps
        | None -> List.rev exps
      )

    | OPif -> (* assumes the list has exactly 3 elements *)
      match l with
        cond :: th :: el :: [] -> (
          let scond = simp cond in
          match tform_to_value scond with
            Some (Bool true) ->
            if Options.simplify_verbose ()
            then
              Format.printf "OP Condition is TRUE@.";
            [simp th]
          | Some (Bool false) ->
            if Options.simplify_verbose ()
            then
              Format.printf "OP Condition is FALSE@.";
            [simp el]
          | _ ->
            if Options.simplify_verbose ()
            then
              Format.printf "OP Condition is UNKNOWN@.";
            [scond; simp th; simp el]
        )
      | _ -> l (* unspecified *)

  let op_term
      (real : bool) (op : value -> value -> value) (t1 : a atterm) (t2 : a atterm)
    : a atterm option =
    match tterm_to_value t1, tterm_to_value t2 with
      Some v1, Some v2 -> (Some (value_to_tterm real (op v1 v2)))
    | _,_ -> None

  let mem_optim (old_a : 'a) (new_a : 'a) : 'a =
    if old_a == new_a then old_a else new_a

  let rec simplify_term_infix
      (op : Symbols.operator) (t1 : a atterm) (t2 : a atterm) : a tt_desc =
    let ty = t1.c.tt_ty in
    let st1, st2 = (simplify_tterm t1), (simplify_tterm t2) in
    let arith oper t1 t2 =
      match tterm_to_value t1, tterm_to_value t2 with
        Some (Num v1), Some (Num v2) ->
        value_to_tdesc (ty = Treal) (Num (oper v1 v2)) |> fst
      | _,_ -> TTinfix (t1, Symbols.Op op, t2) in
    match op with
      Symbols.Plus ->  arith (Num.(+/)) st1 st2
    | Symbols.Minus -> arith (Num.(-/)) st1 st2
    | Symbols.Mult ->  arith (Num.( */ )) st1 st2
    | _ -> TTinfix (st1, Symbols.Op op, st2)

  and simplify_atom (atom : a atatom) : a atatom =
    let map l = List.map simplify_tterm l in
    let c : a tatom =
      match atom.c with
        TAtrue
      | TAfalse -> atom.c
      | TAeq l ->
        let simpl = map l in
        (* the first boolean represents the difference,
           the second that everything is equal *)
        let has_diff l : bool * bool =
          let rec _has_diff (all_equal : bool) (last_val : value option) l : bool * bool =
            match l with
              [] -> false, all_equal
            | hd :: tl ->
              let hd_val = tterm_to_value hd in
              match hd_val, last_val with
              | None, None ->
                if Options.simplify_verbose ()
                then
                  Format.printf "Term %a not valuable@."
                    Typed.print_term hd
                ;
                _has_diff false None tl
              | Some v, None ->
                if Options.simplify_verbose ()
                then
                  Format.printf "Term %a valuable. Keeping it@."
                    Typed.print_term hd;
                _has_diff all_equal (Some v) tl
              | None, Some v ->
                if Options.simplify_verbose ()
                then
                  Format.printf "Term %a not valuable. Keeping %a@."
                    pretty_value v
                    Typed.print_term hd
                ;
                _has_diff all_equal (Some v) tl
              | Some v, Some v' ->
                if val_compare v v' <> 0
                then (
                  if Options.simplify_verbose ()
                  then
                    Format.printf "%a <> %a@."
                      pretty_value v
                      pretty_value v'
                  ;
                  true,false (* There is a trivial difference *)
                )
                else (
                  if Options.simplify_verbose ()
                  then
                    Format.printf "%a = %a@."
                      pretty_value v
                      pretty_value v';
                  _has_diff all_equal (Some v) tl
                )
          in
          _has_diff true None l
        in
        let there_is_diff,all_eq = has_diff simpl in
        if there_is_diff
        then
          (if Options.simplify_verbose ()
           then Format.printf "There is a difference, this is FALSE@." ;
           TAfalse)
        else if all_eq
        then
          (if Options.simplify_verbose ()
           then Format.printf "Everything is equal@." ;
           TAtrue)
        else TAeq simpl

      | TAdistinct l -> TAdistinct (map l)
      | TAneq l -> TAneq (map l)
      | TAle l -> TAle (map l)
      | TAlt l -> TAlt (map l)
      | TApred (term,b) -> TApred (simplify_tterm term, b)
      | TTisConstr (term, name) ->(
        (if Options.simplify_verbose ()
         then Format.printf "TTisConstr (%a,%s)@."
             Typed.print_term term
             (Hstring.view name)
         );
          let term' = simplify_tterm term in
          match term'.c.tt_desc with
          | TTapp (Op (Constr name'),_) ->
            if Hstring.equal name name' then
              TAtrue
            else TAfalse
          | _ -> TTisConstr (term', name)
        )
    in
    let res = mem_optim atom (Annot.mk c)
    in
    if Options.simplify_verbose ()
    then
      Format.printf
        "Old atom: %a\nNew atom: %a\n@."
        Typed.print_atom atom
        Typed.print_atom res;
    res

  and simplify_tform (form : a atform) : a atform =
    let t : a atform = Annot.mk (TFatom (Annot.mk true_atom))
    and f : a atform = Annot.mk (TFatom (Annot.mk false_atom)) in
    let res =
      match form.c with
        TFatom atom -> {form with c = TFatom (simplify_atom atom)}
      | TFop (OPnot, l) -> ({form with c = TFop(OPnot,List.map simplify_tform l)})
      | TFop (op, l) -> (
          let l' =
            oplogic_oper
              ~simp:simplify_tform
              (t,f)
              op
              l
          in
          match l' with
            []  -> assert false
          | hd :: []  ->
            if Options.simplify_verbose ()
            then
              Format.printf
                "Form %a is decided\n@."
                Typed.print_formula hd;
            hd
          | _ ->
            if Options.simplify_verbose ()
            then
              List.iter
                (Format.printf
                   "Form %a is remaining@." Typed.print_formula)
                l';
            {form with c = TFop(op,l')}
        )
      | TFforall qf ->
        let new_qf : a quant_form =
          let sform = simplify_tform qf.qf_form in
          match  tform_to_value sform with
            Some (Bool true) -> (* Result always true *)
            {qf with qf_hyp = []; qf_form = t}
          | Some (Bool false) -> (* Result always false *)
            {qf with qf_hyp = []; qf_form = f}
          | _ ->
            let rev_new_hyp =
              fold_left_stop
                (fun acc hyp ->
                   let shyp = simplify_tform hyp in
                   match tform_to_value shyp with
                     Some (Bool false) -> (* a false hypothesis *)
                     [shyp], true
                   | _ -> (shyp :: acc), false
                )
                []
                qf.qf_hyp
            in
            let new_hyp = List.rev rev_new_hyp in
            {qf with qf_hyp = new_hyp; qf_form = sform}
        in
        {form with c = TFforall new_qf}

      | TFexists qf ->
        let new_qf : a quant_form =
          let sform = simplify_tform qf.qf_form in
          match  tform_to_value sform with
            Some (Bool true) ->
            {qf with qf_hyp = []; qf_form = t}
          | Some (Bool false) ->
            {qf with qf_hyp = []; qf_form = f}
          | _ ->
            let rev_new_hyp =
              fold_left_stop
                (fun acc hyp ->
                   let shyp = simplify_tform hyp in
                   match tform_to_value shyp with
                     Some (Bool true) -> (* a true hypothesis *)
                     [shyp], true
                   | _ -> (shyp :: acc), false
                )
                []
                qf.qf_hyp
            in
            let new_hyp = List.rev rev_new_hyp in
            {qf with qf_hyp = new_hyp; qf_form = sform}
        in
        {form with c = TFforall new_qf}

      | _ -> form (* todo *)
    in
    let res = mem_optim form res in
    if Options.simplify_verbose ()
    then
      Format.printf "Old form: %a\nNew form: %a\n@."
        Typed.print_formula form
        Typed.print_formula res;
    res

  and simplify_ite_desc (cond : a atform) (th : a atterm) (el : a atterm) : a tt_desc =
    let scond = simplify_tform cond in
    let res =
    match tform_to_value scond with
        Some (Bool true) ->
        if Options.simplify_verbose ()
        then
          Format.printf "Condition is TRUE";
        (simplify_tterm th).c.tt_desc
    | Some (Bool false) ->
        if Options.simplify_verbose ()
        then
          Format.printf "Condition is FALSE";
        (simplify_tterm el).c.tt_desc
    | _ ->
        if Options.simplify_verbose ()
        then
          Format.printf "Condition is UNKNOWN";
        TTite (scond, simplify_tterm th, simplify_tterm el) in
    res

  and simplify_tt_desc (desc : a tt_desc) : a tt_desc =
    let res = 
      match desc with
      | TTinfix (term1, Op op, term2) ->
        simplify_term_infix op term1 term2
      | TTinfix (_,_,_) -> assert false (* Could this really happen ? *)
      | TTite (cond, th, el) -> simplify_ite_desc cond th el
      | TTprefix (prefix, term) -> TTprefix (prefix, simplify_tterm term)
      | TTapp (sym, tlist) -> TTapp (sym, List.map simplify_tterm tlist)
      | TTmapsTo (x, term) -> TTmapsTo (x, simplify_tterm term)
      | TTinInterval (term, low, hig) -> TTinInterval (simplify_tterm term, low, hig)
      | TTform f -> TTform (simplify_tform f)
      | _ -> desc
    in
    mem_optim desc res

  and simplify_tterm (term : a atterm) : a atterm =
    let res =
      mem_optim
        term
        {annot = term.annot; c = {term.c with tt_desc = simplify_tt_desc term.c.tt_desc}}
    in

    if Options.simplify_verbose ()
    then
      Format.printf "Old term: %a\nNew term: %a\n@."
        Typed.print_term term
        Typed.print_term res;
    res

  and simplify_tdecl (adecl : a atdecl) : a atdecl =
    let decl =
      match adecl.c with
        TTheory (l,s,te,dlist) ->
        TTheory (l,s,te, List.map simplify_tdecl dlist)

      | TAxiom (l,s,ak,form) ->
        TAxiom (l,s,ak, simplify_tform form)

      | TRewriting _ as res -> res

      | TGoal (l,g,s, form) ->
        TGoal (l,g,s, simplify_tform form)

      | TLogic _ as res -> res

      | TPredicate_def (ln,s,al,form) ->
        TPredicate_def (ln,s,al, simplify_tform form)

      | TFunction_def (l,s,sl,t,form) ->
        TFunction_def (l,s,sl,t, simplify_tform form)

      | TTypeDecl _ as res -> res
    in
    mem_optim adecl {adecl with c = decl}
end

module S = Make (struct type annot = int let mk t = Typed.mk t end)
