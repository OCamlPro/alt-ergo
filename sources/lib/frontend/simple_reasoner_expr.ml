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

(** A simplified formula/expr/... type.
   the diff field is set to false if the operation did not change the
   input.
 *)
type 'a simp =
  {
    v : 'a;
    diff : bool
  }

let get (t : 'a simp) : 'a = t.v
let modified (t : 'a simp) : bool = t.diff

module type S =
sig
  (** The type of annotations *)
  type a

  (** Each of the following function returns a simplified version of the
      atom/formula/desc/tterm/decl in argument.
      Tests multiple properties:
      - replaces trivial equalities by true or false
      - replaces (_ is cons) (cons ...) by true when `cons` is a
        constructor
      - replaces if (cond) then t1 else t2 by t1/t2 when cond is
        simplified by true/false. *)

  val simplify_atom : a atatom -> a atatom simp

  val simplify_tform : a atform -> a atform simp

  val simplify_tt_desc : a tt_desc -> a tt_desc simp

  val simplify_tterm : a atterm -> a atterm simp

  val simplify_tdecl : a atdecl -> a atdecl simp
end

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

module Make
    (Annot :
     sig
       type annot
       val true_form : annot atform
       val false_form : annot atform
       val true_atom : annot atatom
       val false_atom : annot atatom

       val mk : 'a -> ('a, annot) annoted
       val print_annot : annot Typed.annot_printer
     end
    ) =
struct
  let verb = Options.simplify_verbose ()
  let identity l = {v = l; diff = false}
  type a = Annot.annot

  let annot = Annot.print_annot

  let const_to_value (c : tconstant) : value option =
    match c with
    | Tint i -> (
        try Some (Num (Num.num_of_int @@ int_of_string i)) with _ -> None
      )
    | Treal n -> Some (Num n)

    | Ttrue -> Some (Bool true)
    | Tfalse -> Some (Bool false)
    | _ -> None

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
      (f : a atform) : value option =
    if verb
    then
      Format.printf "Valuation of formula %a@."
        (Typed.print_formula ~annot) f;
    match f.c with
      TFatom {c = TAtrue;_} ->  Some (Bool true)
    | TFatom {c = TAfalse;_} -> Some (Bool false)
    | _ -> None

  let tterm_to_value
      ?(simp : a atterm -> a atterm simp = identity) (f : a atterm) : value option =
    let simp_term : a atterm = (simp f).v in
    match simp_term.c.tt_desc with
      TTconst c ->  const_to_value c
    | _ -> None

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
      ?(simp : a atform -> a atform simp = identity)
      (op : oplogic)
      (l : a atform list) : a atform list simp =
    if verb
    then
      Format.printf "Logic operator %s detected.@."
        (Typed.string_of_op op);
    match op with
      OPand -> (
        if verb
        then
          Format.printf "AND formula@.";
        let simp_list : a atform list simp =
          fold_left_stop
             (fun (acc : a atform list simp) elt ->
                let selt : a atform simp = simp elt in
                match tform_to_value selt.v with
                  Some (Bool true) ->
                  if verb
                  then
                    Format.printf "%a is true, removing it from formula@."
                      (Typed.print_formula ~annot) selt.v;
                  {acc with diff = true}, false

                | Some (Bool false) ->
                  if verb
                  then
                    Format.printf "%a is false, ending@."
                      (Typed.print_formula ~annot) selt.v;
                  {v = [Annot.false_form]; diff = true}, true
                | _ ->
                  if verb
                  then
                    Format.printf "%a is unknown@."
                      (Typed.print_formula ~annot) selt.v;
                  {v = selt.v :: acc.v;
                   diff = acc.diff || selt.diff}, false
             )
             {v = []; diff = false}
             l
        in
        if simp_list.v = [] then
          {v = [Annot.true_form]; diff = true}
        else simp_list
      )
    | OPor ->
      let simp =
        fold_left_stop
           (fun (acc : a atform list simp) elt ->
              let selt = simp elt in
              match tform_to_value selt.v with
                Some (Bool true) -> {v = [Annot.true_form]; diff = true}, true
              | Some (Bool false) -> {acc with diff = true}, false
              | _ ->
                  {v = selt.v :: acc.v;
                   diff = acc.diff || selt.diff}, false
           )
           {v = []; diff = false}
           l
      in
      {simp with v = List.rev simp.v}

    | OPxor ->
         let exps, xor =
           List.fold_left
             (fun(* xor is a boolean extracted from trivial exprs*)
               ((acc ,xor): a atform list simp * bool) elt ->
                let selt = simp elt in
                match tform_to_value selt.v with
                  Some (Bool b) -> acc,(xor <> b)
                | _ -> {v = selt.v :: acc.v; diff = acc.diff || selt.diff}, xor
             )
             ({v = []; diff = false}, false)
             l
         in
         if exps.diff
         then (
           if xor
           then {exps with v = Annot.false_form :: List.rev exps.v}
           else {exps with v = Annot.true_form :: List.rev exps.v}
         )
         else exps

    | OPimp -> (
      match l with
        hyp :: conc :: [] -> (
        let shyp,sconc = simp hyp, simp conc in
        match tform_to_value shyp.v, tform_to_value sconc.v with
        | Some (Bool false),_
        | _, Some (Bool true) ->
          {v = [Annot.true_form]; diff = true}

        | Some (Bool true), Some (Bool false) ->
          {v =  [Annot.false_form]; diff = true}
        | _,_ ->
          if shyp.diff || sconc.diff
          then {v = [shyp.v; sconc.v]; diff = true}
          else {v = [hyp; conc]; diff = false}
      )
        | _ -> (* No specification on implications with more than 2 elts *)
          identity l
    )
    | OPnot -> (
        match l with
          [ form ] ->
          let sform = simp form in
          {sform with v = [sform.v]}

        | _ -> identity l
      )
    | OPiff -> (
      let exps, bool_opt =
        fold_left_stop
          (fun (acc,eq) elt : ((a atform list simp * bool option) * bool) ->
             (* eq is a boolean extracted from trivial exprs*)
             let selt = simp elt in
             match tform_to_value selt.v, eq with
               Some (Bool b), Some eq' ->
               if b <> eq'
               then ({v =  [Annot.false_form]; diff = true}, (Some true)), true
               else (acc,eq), false
             | Some (Bool b), _ -> (acc,(Some b)), false
             | _,_ ->
               ({v = selt.v :: acc.v; diff = acc.diff || selt.diff}, eq), false
          )
          ({v = []; diff = false}, None)
          l
      in
        if exps.diff
        then (
          match bool_opt with
            Some true ->
            {v = Annot.true_form :: List.rev exps.v; diff = true}
          | Some false ->
            {v = Annot.false_form :: List.rev exps.v; diff = true}
          | None ->
            {exps with v = Annot.false_form :: List.rev exps.v}
        )
        else
          {exps with v = List.rev exps.v}
    )

    | OPif -> (* assumes the list has exactly 3 elements *)
      match l with
        cond :: th :: el :: [] -> (
          let scond = simp cond in
          match tform_to_value scond.v with
            Some (Bool true) ->
            if verb
            then
              Format.printf "OP Condition is TRUE@.";
            {v = [(simp th).v]; diff = true}
          | Some (Bool false) ->
            if verb
            then
              Format.printf "OP Condition is FALSE@.";
            {v = [(simp el).v]; diff = true}
          | _ ->
            if verb
            then
              Format.printf "OP Condition is UNKNOWN@.";
            let sth, sel = simp th, simp el in
            if sth.v == th && sel.v == el
            then {v = l; diff = false}
            else (
              match tform_to_value sth.v, tform_to_value sel.v with
                Some (Bool true), Some (Bool true) ->
                (* if _ then true else true <=> true *)
                {v = [Annot.true_form]; diff = true}
              | Some (Bool true), Some (Bool false) ->
                (* if cond then true else false <=> cond *)
                {v = [scond.v]; diff = true}
              | Some (Bool false), Some (Bool true) ->
                (* if cond then false else true <=> not cond *)
                let neg_form = Annot.mk (TFop (OPnot, [scond.v])) in
                {v = [neg_form]; diff = true}
              | Some (Bool false), Some (Bool false) ->
                (* if _ then false else false <=> false *)
                {v = [Annot.false_form]; diff = true}
              | _,_ ->
                {v = [scond.v; sth.v; sel.v]; diff = true}
            )
        )
      | _ -> identity l (* unspecified *)

  let map (f : 'a -> 'a simp) (l : 'a list) : 'a list simp =
    let diff = ref false in
    let new_list =
      List.map
        (fun t ->
           let t' = f t in
           if not (t == t'.v)
           then diff := true
             else ();
             t'.v)
          l
      in {v = new_list; diff = !diff}

  (** Returns None if there is no change *)
  let rec simplify_term_infix
      (op : Symbols.operator) (t1 : a atterm) (t2 : a atterm) : a tt_desc option =
    let ty = t1.c.tt_ty in
    let st1, st2 = (simplify_tterm t1), (simplify_tterm t2) in
    let arith oper t1 t2 : a tt_desc option =
      match tterm_to_value t1, tterm_to_value t2 with
        Some (Num v1), Some (Num v2) ->
        Some (value_to_tdesc (ty = Treal) (Num (oper v1 v2)) |> fst)
      | _,_ -> None (* No change *) in
    match op with
      Symbols.Plus ->  arith (Num.(+/)) st1.v st2.v
    | Symbols.Minus -> arith (Num.(-/)) st1.v st2.v
    | Symbols.Mult ->  arith (Num.( */ )) st1.v st2.v
    | _ ->
      if st1.diff || st2.diff then Some (TTinfix (st1.v, Symbols.Op op, st2.v))
      else None

  and simplify_atom (atom : a atatom) : a atatom simp =
    let map l : a atterm list simp = map simplify_tterm l
    in
        (* the first boolean is set to true if one of the op
           returns false, the second that all tests returned true *)
    let oper (op : value -> value -> bool) (l : a atterm list) : bool * bool =
      (* all_true is a boolean stating that every operation succeded.
         set to true at the beginning, it is set to false if one of the
         list term.
         last_val is the last value that has been accepted by the test.
         Set to None at the beginning. *)
      let rec _oper
          (all_true : bool)
          (last_val : value option)
          (l : a atterm list) : bool * bool =
        match l with
          [] -> (* No more elements, and none failed the test. *)
          false, all_true
        | hd :: tl ->
          let hd_val = tterm_to_value hd in
          match hd_val, last_val with
          | None, None ->
            if verb
            then
              Format.printf "Term %a not valuable@."
                (Typed.print_term ~annot) hd
            ;
            _oper false None tl
          | Some v, None ->
            if verb
            then
              Format.printf "Term %a valuable. Keeping it@."
                (Typed.print_term ~annot) hd;
            _oper all_true (Some v) tl
          | None, Some v ->
            if verb
            then
              Format.printf "Term %a not valuable. Keeping %a@."
                pretty_value v
                (Typed.print_term ~annot) hd
            ;
            _oper all_true (Some v) tl
          | Some v, Some v' ->
            if op v v'
            then (
              if verb
              then
                Format.printf "op (%a) (%a) is true @."
                  pretty_value v
                  pretty_value v'
              ; (* We take the new value for the next test,
                   because if op = (<=) for example, we want to keep the
                   highest value *)
              _oper all_true (Some v') tl
            )
            else (
              if verb
              then
                Format.printf "op (%a) (%a) is false@."
                  pretty_value v
                  pretty_value v';
              true,false (* The operation is not respected *)
            )
      in
      _oper true None l
    in
    let apply_op (op : value -> value -> bool) (l : a atterm list) : a atatom simp =
      let simpl = map l in
      let falsify,all_true = oper op simpl.v in
      if falsify
      then {v = Annot.false_atom; diff = true}
      else if all_true
      then {v = Annot.true_atom; diff = true}
      else if simpl.diff
      then {v = (Annot.mk (TAeq simpl.v)); diff = true}
      else {v = atom; diff = false} (* no change, returning the input *)
    in
    let res : a atatom simp =
      match atom.c with
        TAtrue
      | TAfalse -> identity atom (* false = no change *)
      | TAeq l ->
          apply_op (=) l
      | TAdistinct l | TAneq l ->
        apply_op (=) l
      | TAle l ->
        apply_op (fun v1 v2 -> val_compare v1 v2 <= 0) l
      | TAlt l ->
        apply_op (fun v1 v2 -> val_compare v1 v2 < 0) l
      | TApred (term,b) ->
        let term' = simplify_tterm term in
        if term'.diff
        then  {v = Annot.mk (TApred (term'.v, b)); diff = true}
        else {v = atom; diff = false}
      | TTisConstr (term, name) ->(
          (if verb
           then Format.printf "TTisConstr (%a,%s)@."
               (Typed.print_term ~annot) term
               (Hstring.view name)
          );
          let term' = simplify_tterm term in
          match term'.v.c.tt_desc with
          | TTapp (Op (Constr name'),_) ->
            if Hstring.equal name name' then
              {v = Annot.true_atom; diff = true}
            else {v = Annot.false_atom; diff = true}
          | _ ->
            if term'.diff then  {v = Annot.mk (TTisConstr (term'.v, name)); diff = true}
            else {v = atom; diff = false}
        )
    in
    if verb && res.diff
    then
      Format.printf
        "Old atom: %a\nNew atom: %a\n@."
        (Typed.print_atom ~annot) atom
        (Typed.print_atom ~annot) res.v;
    res

  and simplify_tform (form : a atform) : a atform simp =
    let res : a atform simp =
      match form.c with
        TFatom atom ->
        let atom' = simplify_atom atom in
        if atom'.diff then
          {v = Annot.mk (TFatom atom'.v); diff = true}
        else
          {v = form; diff = false}

      | TFop (OPnot, l) ->
        let l' : a atform list simp = map simplify_tform l in
        if l'.diff
        then {v = Annot.mk (TFop(OPnot,l'.v)); diff = true}
        else {v = form; diff = false}

      | TFop (op, l) -> (
          let l' =
            oplogic_oper
              ~simp:simplify_tform
              op
              l
          in
          match l'.v with
            []  -> assert false
          | hd :: []  ->
            {l' with v = hd}
          | _ ->
            if verb
            then
              List.iter
                (Format.printf
                   "Form %a is remaining@." (Typed.print_formula ~annot))
                l'.v;
            {l' with v = Annot.mk (TFop(op,l'.v))}
        )
      | TFforall qf ->
        let new_qf : a quant_form simp =
          let sform = simplify_tform qf.qf_form in
          match  tform_to_value sform.v with
            Some (Bool true) -> (* Result always true *)
            {v = {qf with qf_hyp = []; qf_form = Annot.true_form}; diff = true}
          | Some (Bool false) -> (* Result always false *)
            {v = {qf with qf_hyp = []; qf_form = Annot.false_form}; diff = true}
          | _ ->
            let rev_new_hyp =
              fold_left_stop
                (fun acc hyp ->
                   let shyp = simplify_tform hyp in
                   match tform_to_value shyp.v with
                     Some (Bool false) -> (* a false hypothesis *)
                     {v = [Annot.true_form]; diff = true}, false
                   | _ ->
                     {v = shyp.v :: acc.v; diff = shyp.diff || acc.diff},false
                )
                {v = []; diff = false}
                qf.qf_hyp
            in
            if sform.diff || rev_new_hyp.diff
            then
              let new_hyp = List.rev rev_new_hyp.v in
              {v = {qf with qf_hyp = new_hyp; qf_form = sform.v};
               diff = true}
            else
              identity qf
        in
        if new_qf.diff then
          {v = Annot.mk @@ TFforall new_qf.v; diff = true}
        else
          {v = form; diff = false}

      | TFexists qf ->
        let new_qf : a quant_form simp =
          let sform = simplify_tform qf.qf_form in
          match  tform_to_value sform.v with
            Some (Bool true) -> (* Result always true *)
            {v = {qf with qf_hyp = []; qf_form = Annot.true_form}; diff = true}
          | Some (Bool false) -> (* Result always false *)
            {v = {qf with qf_hyp = []; qf_form = Annot.false_form}; diff = true}
          | _ ->
            let rev_new_hyp =
              fold_left_stop
                (fun acc hyp ->
                   let shyp = simplify_tform hyp in
                   match tform_to_value shyp.v with
                     Some (Bool false) -> (* a false hypothesis *)
                     {v = [Annot.true_form]; diff = true}, false
                   | _ ->
                     {v = shyp.v :: acc.v; diff = shyp.diff || acc.diff},false
                )
                {v = []; diff = false}
                qf.qf_hyp
            in
            if sform.diff || rev_new_hyp.diff
            then
              let new_hyp = List.rev rev_new_hyp.v in
              {v = {qf with qf_hyp = new_hyp; qf_form = sform.v};
               diff = true}
            else
              identity qf
        in
        if new_qf.diff then
          {v = Annot.mk (TFexists new_qf.v); diff = true}
        else
          {v = form; diff = false}

      | _ -> {v = form; diff = false} (* todo *)
    in
    if verb && res.diff
    then
      Format.printf "Old form: %a\nNew form: %a\n@."
        (Typed.print_formula ~annot) form
        (Typed.print_formula ~annot) res.v;
    res

  (** Returns none if there have been no modification *)
  and simplify_ite_desc
      (cond : a atform) (th : a atterm) (el : a atterm) : a tt_desc option =
    let scond = simplify_tform cond in
    match tform_to_value scond.v with
        Some (Bool true) ->
        if verb
        then
          Format.printf "Condition is TRUE";
        let sth = (simplify_tterm th) in
        Some sth.v.c.tt_desc
    | Some (Bool false) ->
        if verb
        then
          Format.printf "Condition is FALSE";
        let sel = (simplify_tterm el) in
        Some sel.v.c.tt_desc
    | _ ->
      if verb
      then
        Format.printf "Condition is UNKNOWN";
      let sth, sel = simplify_tterm th, simplify_tterm el in
      if scond.diff || sth.diff || sel.diff
      then Some (TTite (scond.v, sth.v, sel.v))
      else None

  and simplify_tt_desc (desc : a tt_desc) : a tt_desc simp =
    let res : a tt_desc simp =
      match desc with
      | TTinfix (term1, Op op, term2) -> (
          match simplify_term_infix op term1 term2 with
            None -> {v = desc; diff = false}
          | Some res -> {v = res; diff = true}
        )
      | TTinfix (_,_,_) -> assert false (* Could this really happen ? *)
      | TTite (cond, th, el) -> (
        match simplify_ite_desc cond th el with
            None -> {v = desc; diff = false}
          | Some res -> {v = res; diff = true}
      )
      | TTprefix (prefix, term) ->
        let sterm = simplify_tterm term in
        if sterm.diff then
          {v = TTprefix (prefix, sterm.v);
           diff = true}
        else {v = desc; diff = false}
      | TTapp (sym, tlist) ->
        let l' = map simplify_tterm tlist in
        if l'.diff
        then
          {v = TTapp (sym, l'.v); diff = true}
        else {v = desc; diff = false}
      | TTmapsTo (x, term) ->
        let sterm = simplify_tterm term in
        if sterm.diff then
          {v = TTmapsTo (x, sterm.v);
           diff = true}
        else {v = desc; diff = false}
      | TTinInterval (term, low, hig) ->
        let sterm = simplify_tterm term in
        if sterm.diff then
          {v = TTinInterval (sterm.v, low, hig);
           diff = true}
        else
          {v = desc; diff = false}
      | TTform f ->
        let sf = simplify_tform f in
        if sf.diff
        then {v = TTform sf.v; diff = true}
        else {v = desc; diff = false}
      | _ -> identity desc
    in
    res

  and simplify_tterm (term : a atterm) : a atterm simp =
    let res : a atterm simp =
      let sterm = simplify_tt_desc term.c.tt_desc in
      if sterm.diff then
        {v = Annot.mk {term.c with tt_desc = (sterm.v)}; diff = true}
      else identity term in
    if verb && res.diff
    then
      Format.printf "Old term: %a\nNew term: %a\n@."
        (Typed.print_term ~annot) term
        (Typed.print_term ~annot) res.v;
    res

  and simplify_tdecl (adecl : a atdecl) : a atdecl simp =
    let res =
      match adecl.c with
        TTheory (l,s,te,dlist) ->
        let sdlist = map simplify_tdecl dlist in
        if sdlist.diff
        then
          {v = Annot.mk (TTheory (l,s,te, sdlist.v)); diff = true}
        else identity adecl

      | TAxiom (l,s,ak,form) ->
        let sform = simplify_tform form in
        if sform.diff
        then {v = Annot.mk (TAxiom (l,s,ak, sform.v)); diff = true}
        else identity adecl

      | TGoal (l,g,s, form) ->
        let sform = simplify_tform form in
        if sform.diff
        then {v = Annot.mk (TGoal (l,g,s, sform.v)); diff = true}
        else identity adecl

      | TPredicate_def (ln,s,al,form) ->
        let sform = simplify_tform form in
        if sform.diff
        then {v = Annot.mk (TPredicate_def (ln,s,al, sform.v)); diff = true}
        else identity adecl

      | TFunction_def (l,s,sl,t,form) ->
        let sform = simplify_tform form in
        if sform.diff
        then {v = Annot.mk (TFunction_def (l,s,sl,t, sform.v)); diff = true}
        else identity adecl

      | TRewriting _ | TTypeDecl _ | TLogic _ -> identity adecl in
    if verb && res.diff
    then
      Format.printf "Old decl: %a\nNew decl: %a\n@."
        (Typed.print_atdecl ~annot) adecl
        (Typed.print_atdecl ~annot) res.v;
    res
end

module SInt = Make (
  struct
    type annot = int

    let true_form = Typed.true_atform
    let false_form = Typed.false_atform

    let true_atom = Typed.true_atatom
    let false_atom = Typed.false_atatom

    let mk i = Typed.mk i
    let print_annot = Typed.int_print
  end)
