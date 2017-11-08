(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Parsed
open Typed
open Loc
open Lexing
open Format
open Options

open Gui_config
open Gui_session

let monospace_font = Pango.Font.from_string monospace_font
let general_font = Pango.Font.from_string general_font


let make_indent nb =
  String.make (min max_indent (nb * indent_size)) ' '

type sbuffer = GSourceView2.source_buffer

type error_model = {
  mutable some : bool;
  rcols : GTree.column_list;
  rcol_icon : GtkStock.id GTree.column;
  rcol_desc : String.t GTree.column;
  rcol_line : int GTree.column;
  rcol_type : int GTree.column;
  rcol_color : String.t GTree.column;
  rstore : GTree.list_store;
}

type inst_model = {
  h : (int, Gtk.tree_iter option ref * int ref * string * int ref) Hashtbl.t;
  mutable max : int;
  icols : GTree.column_list;
  icol_icon : GtkStock.id GTree.column;
  icol_desc : String.t GTree.column;
  icol_number : int GTree.column;
  icol_limit : String.t GTree.column;
  icol_tag : int GTree.column;
  istore : GTree.list_store;
}

type timers_model = {
  timers : Timers.t;

  label_sat : GMisc.label;
  label_match : GMisc.label;
  label_cc : GMisc.label;
  label_arith : GMisc.label;
  label_arrays : GMisc.label;
  label_sum : GMisc.label;
  label_records : GMisc.label;
  label_ac : GMisc.label;

  tl_sat : GMisc.label;
  tl_match : GMisc.label;
  tl_cc : GMisc.label;
  tl_arith : GMisc.label;
  tl_arrays : GMisc.label;
  tl_sum : GMisc.label;
  tl_records : GMisc.label;
  tl_ac : GMisc.label;

  pr_sat : GRange.progress_bar;
  pr_match : GRange.progress_bar;
  pr_cc : GRange.progress_bar;
  pr_arith : GRange.progress_bar;
  pr_arrays : GRange.progress_bar;
  pr_sum : GRange.progress_bar;
  pr_records : GRange.progress_bar;
  pr_ac : GRange.progress_bar;
}

type 'a annoted =
    { mutable c : 'a;
      mutable pruned : bool;
      mutable polarity : bool;
      tag : GText.tag;
      ptag : GText.tag;
      id : int;
      buf : sbuffer;
      mutable line : int;
    }

type aterm =
    { at_ty : Ty.t; at_desc : at_desc }

and at_desc =
  | ATconst of tconstant
  | ATvar of Symbols.t
  | ATapp of Symbols.t * aterm list
  | ATinfix of aterm * Symbols.t * aterm
  | ATprefix of Symbols.t * aterm
  | ATget of aterm * aterm
  | ATset of aterm * aterm * aterm
  | ATextract of aterm * aterm * aterm
  | ATconcat of aterm * aterm
  | ATlet of Symbols.t * aterm * aterm
  | ATdot of aterm * Hstring.t
  | ATrecord of (Hstring.t * aterm) list
  | ATnamed of Hstring.t * aterm
  | ATmapsTo of Hstring.t * aterm
  | ATinInterval of aterm * bool * aterm * aterm *  bool
(* bool = true <-> interval is_open *)



type aatom =
  | AAtrue
  | AAfalse
  | AAeq of aterm annoted list
  | AAneq of aterm annoted list
  | AAdistinct of aterm annoted list
  | AAle of aterm annoted list
  | AAlt of aterm annoted list
  | AApred of aterm
  | AAbuilt of Hstring.t * aterm annoted list

type aoplogic =
    AOPand |AOPor | AOPimp | AOPnot | AOPif of aterm | AOPiff

type aquant_form = {
  aqf_bvars : (Symbols.t * Ty.t) list ;
  aqf_upvars : (Symbols.t * Ty.t) list ;
  mutable aqf_triggers : (aterm annoted list * bool) list ;
  aqf_hyp : aform annoted list;
  aqf_form : aform annoted;
}

and aform =
  | AFatom of aatom
  | AFop of aoplogic * aform annoted list
  | AFforall of aquant_form annoted
  | AFexists of aquant_form annoted
  | AFlet of (Symbols.t * Ty.t) list * Symbols.t * aterm * aform annoted
  | AFnamed of Hstring.t * aform annoted

type atyped_decl =
  | ATheory of Loc.t * string * theories_extensions * atyped_decl annoted list
  | AAxiom of Loc.t * string * Parsed.axiom_kind * aform
  | ARewriting of Loc.t * string * ((aterm rwt_rule) annoted) list
  | AGoal of Loc.t * goal_sort * string * aform annoted
  | ALogic of Loc.t * string list * plogic_type
  | APredicate_def of Loc.t * string * (string * ppure_type) list * aform
  | AFunction_def
      of Loc.t * string * (string * ppure_type) list * ppure_type * aform
  | ATypeDecl of Loc.t * string list * string * body_type_decl


type annoted_node =
  | AD of (atyped_decl annoted * Typechecker.env)
  | AF of aform annoted * aform annoted option
  | AT of aterm annoted
  | QF of aquant_form annoted



module MDep = Map.Make (
  struct
    type t = atyped_decl annoted
    let compare = Pervasives.compare
  end)


module MTag = Map.Make (struct
  type t = GText.tag
  let compare t1 t2 = compare t1#get_oid t2#get_oid
end)


type env = {
  buffer : sbuffer;
  goal_view : GSourceView2.source_view;
  inst_buffer : sbuffer;
  inst_view : GSourceView2.source_view;
  errors : error_model;
  insts : inst_model;
  st_ctx : GMisc.statusbar_context;
  mutable ast : (atyped_decl annoted * Typechecker.env) list;
  mutable ctrl : bool;
  mutable last_tag : GText.tag;
  mutable search_tags : GText.tag list;
  mutable proof_tags : int MTag.t;
  mutable proof_toptags : GText.tag list;
  mutable start_select : int option;
  mutable stop_select : int option;
  dep : (atyped_decl annoted list * atyped_decl annoted list) MDep.t;
  actions : action Stack.t;
  saved_actions : action Stack.t;
  resulting_ids : (string * int) list;
}

module HTag = Hashtbl.Make (struct
  type t = GText.tag
  let equal t1 t2 = t1#get_oid = t2#get_oid
  let hash t = t#get_oid
end)




let increase_size envs =
  Pango.Font.set_size monospace_font
    (Pango.Font.get_size monospace_font + 2000);
  (* eprintf "%d +@." (Pango.Font.get_size monospace_font); *)
  List.iter (fun env ->
      env.goal_view#misc#modify_font monospace_font;
      env.inst_view#misc#modify_font monospace_font;
    ) envs;
  Gui_config.update_monospace_font (Pango.Font.to_string monospace_font)


let decrease_size envs =
  (* eprintf "%d +@." (Pango.Font.get_size monospace_font); *)
  Pango.Font.set_size monospace_font
    (Pango.Font.get_size monospace_font - 2000);
  List.iter (fun env ->
      env.goal_view#misc#modify_font monospace_font;
      env.inst_view#misc#modify_font monospace_font;
    ) envs;
  Gui_config.update_monospace_font (Pango.Font.to_string monospace_font)


let reset_size envs =
  Pango.Font.set_size monospace_font
    (Pango.Font.get_size
       (Pango.Font.from_string Gui_config.monospace_font));
  List.iter (fun env ->
      env.goal_view#misc#modify_font monospace_font;
      env.inst_view#misc#modify_font monospace_font;
    ) envs;
  Gui_config.update_monospace_font (Pango.Font.to_string monospace_font)



let set_font envs font =
  let f = Pango.Font.from_string font in
  Pango.Font.set_family monospace_font (Pango.Font.get_family f);
  Pango.Font.set_size monospace_font (Pango.Font.get_size f);
  List.iter (fun env ->
      env.goal_view#misc#modify_font monospace_font;
      env.inst_view#misc#modify_font monospace_font;
    ) envs;
  Gui_config.update_monospace_font (Pango.Font.to_string monospace_font)


type buffer_pending = {
  tags_ranges : ((sbuffer * int * int) list) HTag.t;
}


let pending = {
  tags_ranges = HTag.create 2001;
}

let add_tag_range (b, o1, o2) = function
  | [] -> [b, o1, o2]
  | (c, p1, p2) :: r
      when b#get_oid = c#get_oid && o1 <= p2 + 1 ->
    (c, p1, o2) :: r
  | l -> (b, o1, o2) :: l


let append_buf (buffer:sbuffer)
    ?iter:(iter=buffer#end_iter) ?tags:(tags=[]) s =
  let o1 = iter#offset in
  let o2 = o1 + String.length s in
  buffer#insert ~iter s;
  List.iter (fun t ->
    let bounds =
      try HTag.find pending.tags_ranges t with Not_found -> [] in
    HTag.replace pending.tags_ranges t (add_tag_range (buffer, o1, o2) bounds);
  ) tags

let append_mark (buffer:sbuffer) id =
  ignore(buffer#create_source_mark ~category:(sprintf "trigger_%d" id)
           buffer#end_iter)

let append_indent (buffer:sbuffer) ?iter ?tags indent =
  let indent = min indent max_indents in
  append_buf buffer ?iter ?tags (make_indent indent)

let append_indentation (buffer:sbuffer) ?iter ?tags offset =
  let offset = min offset max_indent in
  append_buf buffer ?iter ?tags (String.make offset ' ')

(* let tags_spaces tags = *)
(*   if List.length tags > 40 then tags else [] *)

let commit_tags_buffer (buffer:sbuffer) =
  HTag.iter (fun t bounds ->
    List.iter (fun (buf, o1, o2) ->
      if buf#get_oid = buffer#get_oid then begin
        let start = buffer#get_iter_at_mark
          (`MARK (buffer#create_mark (buffer#get_iter (`OFFSET o1)))) in
        let stop = buffer#get_iter_at_mark
          (`MARK (buffer#create_mark (buffer#get_iter (`OFFSET o2)))) in
        buffer#apply_tag t ~start ~stop
      end
    ) bounds
  ) pending.tags_ranges;
  HTag.clear pending.tags_ranges

let create_env buf1 tv1 (buf2:sbuffer) tv2 errors insts st_ctx ast dep
    actions resulting_ids=
  let titag = buf2#create_tag [`WEIGHT `BOLD; `UNDERLINE `SINGLE] in
  buf2#insert ~tags:[titag] "User instantiated axioms:\n\n";
  {
    buffer = buf1;
    inst_buffer = buf2;
    goal_view = tv1;
    inst_view = tv2;
    errors = errors;
    insts = insts;
    st_ctx = st_ctx;
    ast = ast;
    dep = dep;
    ctrl = false;
    last_tag = GText.tag ();
    search_tags = [];
    proof_tags = MTag.empty;
    proof_toptags = [];
    start_select = None;
    stop_select = None;
    actions = actions;
    saved_actions = Stack.copy actions;
    resulting_ids = resulting_ids;
  }

let create_replay_env buf1 errors insts ast actions resulting_ids =
  {
    buffer = buf1;
    inst_buffer = GSourceView2.source_buffer ();
    goal_view = GSourceView2.source_view ();
    inst_view = GSourceView2.source_view ();
    errors = errors;
    insts = insts;
    st_ctx = (GMisc.statusbar ())#new_context ~name:"";
    ast = ast;
    dep = MDep.empty;
    ctrl = false;
    last_tag = GText.tag ();
    search_tags = [];
    proof_tags = MTag.empty;
    proof_toptags = [];
    start_select = None;
    stop_select = None;
    actions = actions;
    saved_actions = actions;
    resulting_ids = resulting_ids;
  }

let tag (buffer:sbuffer) = buffer#create_tag []

let new_annot (buffer:sbuffer) c id ptag =
  { c = c; pruned = false; tag = (tag buffer);
    ptag = ptag; id = id; polarity = true; buf = buffer;
    line = buffer#line_count }


let rec findin_aterm tag buffer { at_desc = at_desc } =
  findin_at_desc tag buffer at_desc

and findin_aterm_list tag buffer atl =
  List.fold_left
    (fun r at -> match r with
      | None -> findin_aterm tag buffer at
      | Some _ -> r
    ) None atl

and findin_aaterm tag buffer aat =
  let goodbuf =  aat.buf#get_oid = buffer#get_oid in
  let c = compare tag#priority aat.tag#priority in
  if goodbuf && c = 0 then Some (AT aat)
  else if goodbuf && c > 0 then None
  else findin_aterm tag buffer aat.c

and findin_aaterm_list tag buffer aatl =
  List.fold_left
    (fun r aat -> match r with
      | None -> findin_aaterm tag buffer aat
      | Some _ -> r
    ) None aatl

and findin_at_desc tag buffer = function
  | ATconst _
  | ATvar _ -> None
  | ATapp (s, atl) -> findin_aterm_list tag buffer atl
  | ATinfix (t1, _, t2) | ATget (t1,t2)
  | ATconcat (t1, t2) | ATlet (_, t1, t2) ->
    let r = findin_aterm tag buffer t1 in
    if r == None then findin_aterm tag buffer t2
    else r
  | ATdot (t, _) | ATprefix (_,t) -> findin_aterm tag buffer t
  | ATset (t1, t2, t3) | ATextract (t1, t2, t3)  ->
    let r = findin_aterm tag buffer t1 in
    if r == None then
      let r = findin_aterm tag buffer t2 in
      if r == None then findin_aterm tag buffer t3
      else r
    else r
  | ATrecord r -> let atl = List.map snd r in findin_aterm_list tag buffer atl
  | ATnamed (_, t) -> findin_aterm tag buffer t
  | ATmapsTo (_, t) -> findin_aterm tag buffer t
  | ATinInterval(e, _, i, j, _) -> findin_aterm_list tag buffer [e; i; j]

let findin_aatom tag buffer aa =
  match aa with
    | AAtrue
    | AAfalse -> None

    | AAeq atl
    | AAneq atl
    | AAdistinct atl
    | AAle atl
    | AAlt atl
    | AAbuilt (_, atl) -> findin_aaterm_list tag buffer atl

    | AApred at -> findin_aterm tag buffer at

let rec findin_quant_form tag buffer parent
    {aqf_triggers = trs; aqf_form = aaf ; aqf_hyp } =
  let r = findin_triggers tag buffer trs in
  if r == None then
    let r = findin_aaform_list tag buffer parent aqf_hyp in
    if r == None then
      let goodbuf =  aaf.buf#get_oid = buffer#get_oid in
      let c = compare tag#priority aaf.tag#priority in
      if goodbuf && c = 0 then Some (AF (aaf, parent))
      else if goodbuf && c > 0 then None
      else findin_aform tag buffer (Some aaf) aaf.c
    else r
  else r

and findin_triggers tag buffer trs =
  List.fold_left
    (fun r (aatl,_) -> match r with
      | None -> findin_aaterm_list tag buffer aatl
      | Some _ -> r
    ) None trs

and findin_aform tag buffer parent aform =
  match aform with
    | AFatom a -> findin_aatom tag buffer a
    | AFop (op, afl) -> findin_aaform_list tag buffer parent afl
    | AFforall qf
    | AFexists qf ->
      let goodbuf =  qf.buf#get_oid = buffer#get_oid in
      let c = compare tag#priority qf.tag#priority in
      if goodbuf && c = 0 then Some (QF qf)
      else if goodbuf && c > 0 then None
      else findin_quant_form tag buffer parent qf.c
    | AFlet (vs, s, t, aaf) ->
      let r = findin_aterm tag buffer t in
      if r == None then findin_aaform tag buffer parent aaf
      else r
    | AFnamed (_, aaf) ->
      findin_aform tag buffer parent aaf.c

and findin_aaform_list tag buffer parent aafl =
  List.fold_left
    (fun r aaf -> match r with
      | None -> findin_aaform tag buffer parent aaf
      | Some _ -> r
    ) None aafl

and findin_aaform tag buffer parent aaf =
  let goodbuf =  aaf.buf#get_oid = buffer#get_oid in
  let c = compare tag#priority aaf.tag#priority in
  if goodbuf && c = 0 then Some (AF (aaf, parent))
  else if goodbuf && c > 0 then None
  else findin_aform tag buffer (Some aaf) aaf.c

let rec findin_atyped_delc tag buffer (td, env) stop_decl =
  let goodbuf =  td.buf#get_oid = buffer#get_oid in
  let c = compare tag#priority td.tag#priority in
  if goodbuf && c = 0 then Some (AD (td, env))
  else if goodbuf && c > 0 then None
  else if stop_decl then Some (AD (td, env))
  else match td.c with
    | ATheory (loc, name, ext, decls) ->
      List.fold_left
        (fun acc d ->
          if acc != None then acc
          else findin_atyped_delc tag buffer (d, env) stop_decl
        )None decls
    | AAxiom (_, _, _, af)
    | APredicate_def (_, _, _, af)
    | AFunction_def (_, _, _, _, af) ->
      let aaf = new_annot buffer af (-1) tag in
	(* TODO: Change this so af is annoted *)
      findin_aform tag buffer (Some aaf) af
    | ARewriting (_, _, rwtl) -> None
    (*List.fold_left
      (fun {rwt_left = rl; rwt_right = rr} acc -> match acc with
      | Some _ -> acc
      | None -> findin_aterm_list tag buffer [rl; rr]
      ) rwtl None*)
    | AGoal (_, _, _, aaf) ->
      let goodbuf =  aaf.buf#get_oid = buffer#get_oid in
      let c = compare tag#priority aaf.tag#priority in
      if goodbuf && c = 0 then Some (AF (aaf, None))
      else if goodbuf && c > 0 then None
      else findin_aform tag buffer (Some aaf) aaf.c
    | ALogic _
    | ATypeDecl _ ->
      None

let find_aux stop_decl tag buffer l =
  List.fold_left
    (fun r td -> match r with
      | None -> findin_atyped_delc tag buffer td stop_decl
      | Some _ -> r
    ) None l

let find = find_aux false

let find_decl = find_aux true




let rec print_ppure_type fmt = function
  | PPTunit -> fprintf fmt "unit"
  | PPTint -> fprintf fmt "int"
  | PPTbool -> fprintf fmt "bool"
  | PPTreal -> fprintf fmt "real"
  | PPTbitv size -> fprintf fmt "bitv[%d]" size
  | PPTvarid (s, loc) -> fprintf fmt "\'%s" s
  (* | PPTfarray pp -> fprintf fmt "%a farray" print_ppure_type pp *)
  | PPTexternal ([], s, loc) ->
    fprintf fmt "%s" s
  | PPTexternal (pptypes, s, loc) ->
    fprintf fmt "%a %s" (print_ppure_type_list true) pptypes s

and print_ppure_type_list nested fmt l =
  let rec aux fmt = function
    | [] -> ()
    | [p] -> print_ppure_type fmt p
    | p::r -> fprintf fmt "%a, %a" print_ppure_type p aux r
  in
  if not nested then aux fmt l
  else match l with
    | [] -> ()
    | [s] -> aux fmt l
    | s::r -> fprintf fmt "(%a)" aux l

let print_plogic_type fmt = function
  | PPredicate [] -> fprintf fmt "prop"
  | PPredicate pptl ->
    fprintf fmt "%a -> prop" (print_ppure_type_list false) pptl
  | PFunction ([], ppt) ->
    fprintf fmt "%a" print_ppure_type ppt
  | PFunction (pptl, ppt) ->
    fprintf fmt "%a -> %a" (print_ppure_type_list false) pptl
      print_ppure_type ppt


let print_tconstant fmt = function
  | Tvoid -> fprintf fmt "void"
  | Ttrue -> fprintf fmt "true"
  | Tfalse -> fprintf fmt "false"
  | Tint s -> fprintf fmt "%s" s
  | Treal n -> fprintf fmt "%s" (Num.string_of_num n)
  | Tbitv s -> fprintf fmt "%s" s

let tconstant_to_string = function
  | Tvoid -> "void"
  | Ttrue -> "true"
  | Tfalse -> "false"
  | Tint s -> s
  | Treal (Num.Int i) -> string_of_int i ^ "."
  | Treal (Num.Big_int i) -> Big_int.string_of_big_int i ^ "."
  | Treal (Num.Ratio r) ->
    Big_int.string_of_big_int (Ratio.numerator_ratio r) ^ "./" ^
    Big_int.string_of_big_int (Ratio.denominator_ratio r) ^ "."
  | Tbitv s -> s

let rec print_var_list fmt = function
  | [] -> ()
  | [s,ty] -> fprintf fmt "%a:%a" Symbols.print_clean s Ty.print ty
  | (s,ty)::l ->
    fprintf fmt "%a:%a, %a" Symbols.print_clean s Ty.print ty print_var_list l


let rec print_string_sep sep fmt = function
  | [] -> ()
  | [s] -> fprintf fmt "%s" s
  | s::r -> fprintf fmt "%s%s%a" s sep (print_string_sep sep) r

let rec print_string_list fmt = print_string_sep ", " fmt

let print_astring_list fmt l =
  let rec aux fmt = function
    | [] -> ()
    | [s] -> fprintf fmt "\'%s" s
    | s::r -> fprintf fmt "\'%s, %a" s aux r
  in
  match l with
    | [] -> ()
    | [s] -> aux fmt l
    | s::r -> fprintf fmt "(%a)" aux l

let rec print_string_ppure_type_list fmt = function
  | [] -> ()
  | [s,ppt] -> fprintf fmt "%s:%a" s print_ppure_type ppt
  | (s,ppt)::l -> fprintf fmt "%s:%a, %a" s print_ppure_type ppt
    print_string_ppure_type_list l

let print_pred_type_list fmt = function
  | [] -> ()
  | l -> fprintf fmt "(%a)" print_string_ppure_type_list l


(**************** to delete *******************)

let rec print_tterm fmt {Typed.c= {tt_desc = tt_desc}} =
  print_tt_desc fmt tt_desc

and print_tterm_list se fmt = function
  | [] -> ()
  | [t] -> print_tterm fmt t
  | t::r -> fprintf fmt "%a%s%a" print_tterm t se (print_tterm_list se) r

and print_record se fmt = function
  | [] -> ()
  | [c,t] -> fprintf fmt "%s = %a" (Hstring.view c) print_tterm t
  | (c,t)::r ->
    fprintf fmt "%s = %a%s%a" (Hstring.view c)
      print_tterm t se (print_record se) r


and print_tt_desc fmt = function
  | TTconst c -> print_tconstant fmt c
  | TTvar s -> Symbols.print_clean fmt s
  | TTapp (f, ts) ->
    fprintf fmt "%a(%a)" Symbols.print_clean f (print_tterm_list ", ") ts
  | TTinfix (t1, s, t2) ->
    fprintf fmt "%a %a %a" print_tterm t1 Symbols.print_clean s print_tterm t2
  | TTprefix (s, t) ->
    fprintf fmt "%a %a" Symbols.print_clean s print_tterm t
  | TTlet (s, t1, t2) ->
    fprintf fmt "let %a = %a in %a"
      Symbols.print_clean s print_tterm t1 print_tterm t2
  | TTconcat (t1, t2) ->
    fprintf fmt "%a@%a" print_tterm t1 print_tterm t2
  | TTextract (t, t1, t2) ->
    fprintf fmt "%a^{%a;%a}" print_tterm t print_tterm t1 print_tterm t2
  | TTset (t, t1, t2) ->
    fprintf fmt "%a[%a<-%a]" print_tterm t print_tterm t1 print_tterm t2
  | TTget (t, t1) ->
    fprintf fmt "%a[%a]" print_tterm t print_tterm t1
  | TTdot (t, c) ->
    fprintf fmt "%a.%s" print_tterm t (Hstring.view c)
  | TTrecord r -> fprintf fmt "{ %a }" (print_record ";") r
  | TTnamed (lbl, t) -> fprintf fmt "%s:%a" (Hstring.view lbl) print_tterm t
  | TTinInterval(e, lb, i, j, ub) ->
    fprintf fmt "%a in %s%a, %a%s"
      print_term e
      (if lb then "]" else "[")
      print_term i
      print_term j
      (if ub then "[" else "]")

  | TTmapsTo(x,e) ->
    fprintf fmt "%s |-> %a" (Hstring.view x) print_term e

let print_tatom fmt a = match a.Typed.c with
  | TAtrue -> fprintf fmt "true"
  | TAfalse -> fprintf fmt "false"
  | TAeq tl -> print_tterm_list " = " fmt tl
  | TAneq tl -> print_tterm_list " <> " fmt tl
  | TAdistinct tl ->
    fprintf fmt "distinct(%a)" (print_tterm_list ", ") tl
  | TAle tl -> print_tterm_list " <= " fmt tl
  | TAlt tl -> print_tterm_list " < " fmt tl
  | TApred t -> print_tterm fmt t
  | TAbuilt (h, tl) -> print_tterm_list (" "^(Hstring.view h)^" ") fmt tl

let print_oplogic fmt = function
  | OPand -> fprintf fmt "and"
  | OPor -> fprintf fmt "or"
  | OPimp -> fprintf fmt "->"
  | OPnot -> fprintf fmt "not"
  | OPif t -> fprintf fmt "%a ->" print_tterm t
  | OPiff -> fprintf fmt "<->"

let print_rwt fmt { rwt_vars = rv; rwt_left = rl; rwt_right = rr } =
  fprintf fmt "forall %a. %a = %a"
    print_var_list rv print_tterm rl print_tterm rr

let rec print_rwt_list fmt = function
  | [] -> ()
  | [rwt] -> print_rwt fmt rwt
  | rwt::l -> fprintf fmt "%a; %a" print_rwt rwt print_rwt_list l

let rec print_quant_form fmt
    {qf_bvars = bv; qf_upvars = uv; qf_triggers = trs; qf_form = tf } =
  fprintf fmt "%a [%a]. %a"
    print_var_list bv print_triggers trs print_tform tf

and print_triggers fmt = function
  | [] -> ()
  | [ts,_] -> print_tterm_list ", " fmt ts
  | (ts,_)::l -> fprintf fmt "%a | %a" (print_tterm_list ", ") ts print_triggers l

and print_tform2 fmt f = match f.Typed.c with
  | TFatom a -> print_tatom fmt a
  | TFop (OPnot, [tf]) -> fprintf fmt "not %a" print_tform tf
  | TFop (op, tfl) -> print_tform_list op fmt tfl
  | TFforall qf -> fprintf fmt "forall %a" print_quant_form qf
  | TFexists qf -> fprintf fmt "exists %a" print_quant_form qf
  | TFlet (vs, s, t, tf) ->
    fprintf fmt "let %a = %a in\n %a"
      Symbols.print_clean s print_tterm t print_tform tf
  | TFnamed (_, tf) -> print_tform fmt tf

and print_tform fmt f = fprintf fmt " (id:%d)%a" f.Typed.annot print_tform2 f

and print_tform_list op fmt = function
  | [] -> ()
  | [tf] -> print_tform fmt tf
  | tf::l -> fprintf fmt "%a %a %a"
    print_tform tf print_oplogic op (print_tform_list op) l

let rec print_record_type fmt = function
  | [] -> ()
  | [c, ty] -> fprintf fmt "%s : %a" c print_ppure_type ty
  | (c, ty)::l ->
    fprintf fmt "%s : %a; %a" c print_ppure_type ty print_record_type l

let rec print_typed_decl fmt td = match td.Typed.c with
  | TAxiom (_, s, Parsed.Default, tf) ->
    fprintf fmt "axiom %s : %a" s print_tform tf
  | TAxiom (_, s, Parsed.Propagator, tf) ->
    fprintf fmt "axiom %s : %a" s print_tform tf
  | TRewriting (_, s, rwtl) ->
    fprintf fmt "rewriting %s : %a" s print_rwt_list rwtl
  | TGoal (_, Thm, s, tf) -> fprintf fmt "goal %s : %a" s print_tform tf
  | TGoal (_, Check, s, tf) -> fprintf fmt "check %s : %a" s print_tform tf
  | TGoal (_, Cut, s, tf) -> fprintf fmt "cut %s : %a" s print_tform tf
  | TLogic (_, ls, ty) ->
    fprintf fmt "logic %a : %a" print_string_list ls print_plogic_type ty
  | TPredicate_def (_, p, spptl, tf) ->
    fprintf fmt "predicate %s %a = %a" p
      print_pred_type_list spptl print_tform tf
  | TFunction_def (_, f, spptl, ty, tf) ->
    fprintf fmt "function %s (%a) : %a = %a" f
      print_string_ppure_type_list spptl print_ppure_type ty print_tform tf
  | TTypeDecl (_, ls, s, Abstract) ->
    fprintf fmt "type %a %s" print_astring_list ls s
  | TTypeDecl (_, ls, s, Enum lc) ->
    fprintf fmt "type %a %s = %a" print_astring_list ls s
      (print_string_sep " | ") lc
  | TTypeDecl (_, ls, s, Record rt) ->
    fprintf fmt "type %a %s = %a" print_astring_list ls s print_record_type rt

  | TTheory (loc, name, th_ext, decls) ->
    fprintf fmt "theory %s exetends %s =\n%a\nend@."
      (Typed.string_of_th_ext th_ext) name
      (fun fmt -> List.iter (print_typed_decl fmt)) decls

let print_typed_decl_list fmt = List.iter (fprintf fmt "%a@." print_typed_decl)

(**********************************************)



(****************** Computing dependancies ***********************)

let find_dep_by_string dep s =
  MDep.fold
    (fun d _ found ->
      match found with
	| Some _ -> found
	| None -> begin
	  match d.c with
	    | ALogic (_, ls, ty) when List.mem s ls -> Some d
	    | ATypeDecl (_, _, s', _) when Pervasives.(=) s s'-> Some d
	    | APredicate_def (_, p, _, _) when Pervasives.(=) s p -> Some d
	    | AFunction_def (_, f, _, _, _) when Pervasives.(=) s f -> Some d
	    | _ -> None
	end
    ) dep None

let find_tag_deps dep tag =
  MDep.fold
    (fun d (deps,_) found ->
      match found with
	| Some _ -> found
	| None -> if Pervasives.(=) d.tag tag then Some deps else None
    ) dep None

let find_tag_inversedeps dep tag =
  MDep.fold
    (fun d (_,deps) found ->
      match found with
	| Some _ -> found
	| None -> if Pervasives.(=) d.tag tag then Some deps else None
    ) dep None

let make_dep_string d ex dep s =
  if not (List.mem s ex) then
    let m = find_dep_by_string dep s in
    match m with
      | None -> dep
      | Some d' ->
	let deps, depsi =
	  try MDep.find d' dep
	  with Not_found -> [], [] in
	let dep = MDep.add d' (deps, d::depsi) dep in
	let deps, depsi =
	  try MDep.find d dep
	  with Not_found -> [], [] in
	MDep.add d (d'::deps, depsi) dep
  else dep

let rec make_dep_aterm d ex dep {at_desc = at_desc; at_ty = at_ty } =
  make_dep_at_desc d ex dep at_desc

and make_dep_aaterm d ex dep aat = make_dep_aterm d ex dep aat.c

and make_dep_at_desc d ex dep = function
  | ATconst _ -> dep
  | ATvar s  -> make_dep_string d ex dep (Symbols.to_string_clean s)
  | ATapp (s, atl)  ->
    let dep = make_dep_string d ex dep (Symbols.to_string_clean s) in
    List.fold_left (make_dep_aterm d ex) dep atl
  | ATinfix (t1, s, t2)  ->
    let dep = make_dep_aterm d ex dep t1 in
    let dep = make_dep_string d ex dep (Symbols.to_string_clean s) in
    make_dep_aterm d ex dep t2
  | ATprefix (s, t) ->
    let dep = make_dep_string d ex dep (Symbols.to_string_clean s) in
    make_dep_aterm d ex dep t
  | ATget (t1, t2) | ATconcat (t1, t2) ->
    let dep = make_dep_aterm d ex dep t1 in
    make_dep_aterm d ex dep t2
  | ATset (t1, t2, t3) | ATextract (t1, t2, t3)  ->
    let dep = make_dep_aterm d ex dep t1 in
    let dep = make_dep_aterm d ex dep t2 in
    make_dep_aterm d ex dep t3
  | ATlet (s, t1, t2) ->
    let dep = make_dep_string d ex dep (Symbols.to_string_clean s) in
    let dep = make_dep_aterm d ex dep t1 in
    make_dep_aterm d ex dep t2
  | ATdot (t, c) ->
    let dep = make_dep_string d ex dep (Hstring.view c) in
    make_dep_aterm d ex dep t
  | ATrecord r ->
    List.fold_left
      (fun dep (c, t) ->
	let dep = make_dep_string d ex dep (Hstring.view c) in
	make_dep_aterm d ex dep t)
      dep r
  | ATnamed (_, t) -> make_dep_aterm d ex dep t
  | ATmapsTo (_, t) -> make_dep_aterm d ex dep t
  | ATinInterval(e, _, i, j, _) ->
    List.fold_left (make_dep_aterm d ex) dep [e; i; j]

let make_dep_aatom d ex dep = function
  | AAtrue | AAfalse -> dep
  | AAeq atl | AAneq atl | AAdistinct atl | AAle atl | AAlt atl ->
    List.fold_left (make_dep_aaterm d ex) dep atl
  | AApred at -> make_dep_aterm d ex dep at
  | AAbuilt (h, atl) -> List.fold_left (make_dep_aaterm d ex) dep atl

let make_dep_oplogic d ex dep = function
  | AOPif at -> make_dep_aterm d ex dep at
  | _ -> dep

let rec make_dep_quant_form d ex dep
    {aqf_bvars = bv; aqf_upvars = uv; aqf_triggers = trs; aqf_form = aaf } =
  let vars = List.map (fun (s,_) -> (Symbols.to_string_clean s)) bv in
  make_dep_aform d (vars@ex) dep aaf.c

and make_dep_aform d ex dep = function
  | AFatom a -> make_dep_aatom d ex dep a
  | AFop (op, afl) ->
    List.fold_left (make_dep_aaform d ex) dep afl
  | AFforall qf -> make_dep_quant_form d ex dep qf.c
  | AFexists qf -> make_dep_quant_form d ex dep qf.c
  | AFlet (vs, s, t, aaf) ->
    let dep = make_dep_aterm d ex dep t in
    make_dep_aaform d ex dep aaf
  | AFnamed (_, aaf) ->
    make_dep_aform d ex dep aaf.c

and make_dep_aaform d ex dep aaf = make_dep_aform d ex dep aaf.c

let rec make_dep_atyped_decl dep d =
  match d.c with
    | ATheory (loc, name, ext, decls) ->
      List.fold_left (fun dep d -> make_dep_atyped_decl dep d) dep decls
    | AAxiom (loc, s, _, af) -> make_dep_aform d [] dep af
    | ARewriting (loc, s, arwtl) ->
      List.fold_left
	(fun dep r ->
	  let vars = List.map
	    (fun (s,_) -> (Symbols.to_string_clean s)) r.c.rwt_vars in
	  let dep = make_dep_aterm d vars dep r.c.rwt_left in
	  make_dep_aterm d vars dep r.c.rwt_right
	) dep arwtl
    | AGoal (loc, _, s, aaf) -> make_dep_aform d [] dep aaf.c
    | ALogic (loc, ls, ty) -> MDep.add d ([], []) dep
    | APredicate_def (loc, p, spptl, af) ->
      let dep = MDep.add d ([], []) dep in
      make_dep_aform d (p::(List.map fst spptl)) dep af
    | AFunction_def (loc, f, spptl, ty, af) ->
      let dep = MDep.add d ([], []) dep in
      make_dep_aform d (f::(List.map fst spptl)) dep af
    | ATypeDecl (loc, ls, s, lc) -> MDep.add d ([], []) dep

let make_dep annoted_ast =
  let dep = MDep.empty in
  List.fold_left (fun dep (t,_) -> make_dep_atyped_decl dep t) dep annoted_ast


(* Translation from AST to annoted/pruned AST *)


let annot_of_tconstant (buffer:sbuffer)  t =
  new_annot buffer t

let rec of_tterm (buffer:sbuffer) t =
  {at_desc = of_tt_desc buffer t.Typed.c.tt_desc;
   at_ty = t.Typed.c.tt_ty }

and annot_of_tterm (buffer:sbuffer) t =
  let ptag = tag buffer in
  let c = of_tterm buffer t in
  new_annot buffer c t.Typed.annot ptag

and of_tt_desc (buffer:sbuffer) = function
  | TTconst c -> (ATconst c)
  | TTvar s  ->(ATvar s)
  | TTapp (s, tts)  ->
    ATapp (s, List.map (of_tterm buffer ) tts)
  | TTinfix (t1, s, t2)  ->
    ATinfix (of_tterm buffer t1, s, of_tterm buffer t2)
  | TTprefix (s,t) -> ATprefix (s, of_tterm buffer t)
  | TTget (t1, t2) -> ATget (of_tterm buffer t1, of_tterm buffer t2)
  | TTset (t, t1, t2) ->
    ATset (of_tterm buffer t, of_tterm buffer t1, of_tterm buffer t2)
  | TTextract (t, t1, t2) ->
    ATextract (of_tterm buffer t, of_tterm buffer t1, of_tterm buffer t2)
  | TTconcat (t1, t2) -> ATconcat (of_tterm buffer t1, of_tterm buffer t2)
  | TTlet (s, t1, t2) -> ATlet (s, of_tterm buffer t1, of_tterm buffer t2)
  | TTdot (t, c) -> ATdot (of_tterm buffer t, c)
  | TTrecord r -> ATrecord (List.map (fun (c,t) -> (c, of_tterm buffer t)) r)
  | TTnamed (lbl, t) -> ATnamed (lbl, of_tterm buffer t)
  | TTmapsTo (hs, t) -> ATmapsTo (hs, of_tterm buffer t)
  | TTinInterval(e, lb, i, j, ub) ->
    ATinInterval(
      of_tterm buffer e,
      lb,
      of_tterm buffer i,
      of_tterm buffer j,
      ub
    )


let of_tatom (buffer:sbuffer) a = match a.Typed.c with
  | TAtrue -> AAtrue
  | TAfalse -> AAfalse
  | TAeq tl -> AAeq (List.map (annot_of_tterm buffer ) tl)
  | TAneq tl -> AAneq (List.map (annot_of_tterm buffer ) tl)
  | TAdistinct tl -> AAdistinct (List.map (annot_of_tterm buffer ) tl)
  | TAle tl -> AAle (List.map (annot_of_tterm buffer ) tl)
  | TAlt tl -> AAlt (List.map (annot_of_tterm buffer ) tl)
  | TApred t -> AApred (of_tterm buffer  t)
  | TAbuilt (h, tl) -> AAbuilt (h, (List.map (annot_of_tterm buffer ) tl))

let of_oplogic (buffer:sbuffer)  = function
  | OPand -> AOPand
  | OPor -> AOPor
  | OPimp -> AOPimp
  | OPnot -> AOPnot
  | OPif t -> AOPif (of_tterm buffer  t)
  | OPiff -> AOPiff

let rec change_polarity_aform f =
  f.polarity <- not f.polarity;
  match f.c with
    | AFatom _ -> ()
    | AFop (_, afl) -> List.iter change_polarity_aform afl
    | AFforall aaqf | AFexists aaqf ->
      aaqf.polarity <- not aaqf.polarity;
      change_polarity_aform aaqf.c.aqf_form
    | AFlet (_,_,_,af) | AFnamed (_, af) -> change_polarity_aform af


let rec of_quant_form (buffer:sbuffer)
    {qf_bvars = bv; qf_upvars = uv; qf_triggers = trs; qf_form = tf; qf_hyp } =
  let ptag = tag buffer in
  { aqf_bvars = bv;
    aqf_upvars = uv;
    aqf_triggers =
      List.map (fun (l,b) -> List.map (annot_of_tterm buffer) l, b) trs;
    aqf_hyp = List.map (annot_of_tform buffer) qf_hyp;
    aqf_form = new_annot buffer (of_tform buffer tf) tf.Typed.annot ptag;
  }

and annot_of_quant_form (buffer:sbuffer) qf id =
  let ptag = tag buffer in
  new_annot buffer (of_quant_form buffer qf) id ptag

and of_tform (buffer:sbuffer) f = match f.Typed.c with
  | TFatom a -> AFatom (of_tatom buffer a)
  | TFop (op, tfl) ->
    let afl = List.map (annot_of_tform buffer ) tfl in
    assert (let l = List.length afl in l >= 1 && l <= 2);
    if op == OPnot || op == OPimp then
      change_polarity_aform (List.hd afl);
    AFop (of_oplogic buffer  op, afl)
  | TFforall qf -> AFforall (annot_of_quant_form buffer qf f.Typed.annot)
  | TFexists qf -> AFexists (annot_of_quant_form buffer qf f.Typed.annot)
  | TFlet (vs, s, t, tf) ->
    AFlet (vs, s, of_tterm buffer  t, annot_of_tform buffer tf)
  | TFnamed (n, tf) ->
    AFnamed (n, annot_of_tform buffer tf)

and annot_of_tform (buffer:sbuffer) t =
  let ptag = tag buffer in
  let c = of_tform buffer t in
  new_annot buffer c t.Typed.annot ptag

let rec annot_of_typed_decl (buffer:sbuffer) td =
  let ptag = tag buffer in
  let c = match td.Typed.c with
    | TTheory (loc, name, ext, decls) ->
      ATheory (loc, name, ext,
               List.map (fun d -> annot_of_typed_decl buffer d) decls)
    | TAxiom (loc, s, ax_kd, tf) -> AAxiom (loc, s, ax_kd, of_tform buffer tf)
    | TRewriting (loc, s, rwtl) ->
      let arwtl = List.map
	(fun rwt ->
	  new_annot buffer
	    { rwt with
	      rwt_left = of_tterm buffer rwt.rwt_left;
	      rwt_right = of_tterm buffer rwt.rwt_right }
	    td.Typed.annot ptag
	) rwtl in
      ARewriting (loc, s, arwtl)
    | TGoal (loc, gs, s, tf) ->
      let g = new_annot buffer (of_tform buffer tf) tf.Typed.annot ptag in
      AGoal (loc, gs, s, g)
    | TLogic (loc, ls, ty) -> ALogic (loc, ls, ty)
    | TPredicate_def (loc, p, spptl, tf) ->
      APredicate_def (loc, p,  spptl, of_tform buffer  tf)
    | TFunction_def (loc, f, spptl, ty, tf) ->
      AFunction_def (loc, f,  spptl, ty, of_tform buffer  tf)
    | TTypeDecl (loc, ls, s, lc) -> ATypeDecl (loc, ls, s, lc)
  in
  new_annot buffer c td.Typed.annot ptag


let annot (buffer:sbuffer) ast =
  List.map (fun (t,env) -> (annot_of_typed_decl buffer t, env)) ast

(* Translation from annoted/pruned AST to AST *)

let rec to_tterm id {at_desc = at_desc; at_ty = at_ty } =
  {Typed.c = { tt_desc = to_tt_desc at_desc; tt_ty = at_ty };
   Typed.annot = id }

and from_aaterm_list = function
  | [] -> []
  | at::l ->
    if at.pruned then from_aaterm_list l
    else (to_tterm at.id at.c)::(from_aaterm_list l)

and to_tt_desc = function
  | ATconst c -> TTconst c
  | ATvar s  -> TTvar s
  | ATapp (s, atl)  -> TTapp (s, List.map (to_tterm 0) atl)
  | ATinfix (t1, s, t2) -> TTinfix (to_tterm 0 t1, s, to_tterm 0 t2)
  | ATprefix (s, t) -> TTprefix (s, to_tterm 0 t)
  | ATget (t1, t2) -> TTget (to_tterm 0 t1, to_tterm 0 t2)
  | ATset (t1, t2, t3) -> TTset (to_tterm 0 t1, to_tterm 0 t2, to_tterm 0 t3)
  | ATextract (t1, t2, t3) ->
    TTextract (to_tterm 0 t1, to_tterm 0 t2, to_tterm 0 t3)
  | ATconcat (t1, t2) -> TTconcat (to_tterm 0 t1, to_tterm 0 t2)
  | ATlet (s, t1, t2) -> TTlet (s, to_tterm 0 t1, to_tterm 0 t2)
  | ATdot (t, c) -> TTdot (to_tterm 0 t, c)
  | ATrecord r -> TTrecord (List.map (fun (c, t) -> (c, to_tterm 0 t)) r)
  | ATnamed (lbl, t) -> TTnamed (lbl, to_tterm 0 t)
  | ATmapsTo (hs, t) -> TTmapsTo (hs, to_tterm 0 t)
  | ATinInterval(e, lb, i, j, ub) ->
    TTinInterval(
      to_tterm 0 e,
      lb,
      to_tterm 0 i,
      to_tterm 0 j,
      ub
    )

let to_tatom aa id =
  let c = match aa with
    | AAtrue -> TAtrue
    | AAfalse -> TAfalse
    | AAeq atl -> TAeq (from_aaterm_list atl)
    | AAneq atl -> TAneq (from_aaterm_list atl)
    | AAdistinct atl -> TAdistinct (from_aaterm_list atl)
    | AAle atl -> TAle (from_aaterm_list atl)
    | AAlt atl -> TAlt (from_aaterm_list atl)
    | AApred at -> TApred (to_tterm 0 at)
    | AAbuilt (h, atl) -> TAbuilt (h, (from_aaterm_list atl))
  in
  { Typed.c = c;
    Typed.annot = id }

let to_oplogic = function
  | AOPand -> OPand
  | AOPor -> OPor
  | AOPimp  -> OPimp
  | AOPnot -> OPnot
  | AOPif at -> OPif (to_tterm 0 at)
  | AOPiff -> OPiff

let rec to_quant_form
    {aqf_bvars = bv; aqf_upvars = uv; aqf_triggers = trs; aqf_form = aaf;
     aqf_hyp } =
  { qf_bvars = bv;
    qf_upvars = uv;
    qf_triggers = to_triggers trs;
    qf_hyp = from_aaform_list aqf_hyp;
    qf_form = to_tform aaf;
  }

and to_triggers = function
  | [] -> []
  | (atl,b)::l ->
    let l' = from_aaterm_list atl in
    if l' == [] then to_triggers l
    else (l', b)::(to_triggers l)

and void_to_tform af id =
  let c = match af with
    | AFatom a -> TFatom (to_tatom a id)
    | AFop (op, afl) ->
      let tfl = from_aaform_list afl in
      let op = to_oplogic op in
      begin
	match tfl, op with
	  | [], _ -> failwith "Empty logic operation"
	  | [tf], OPnot -> TFop (op, tfl)
	  | [tf], _ -> tf.Typed.c
	  | _ -> TFop (op, tfl)
      end
    | AFforall qf -> TFforall (to_quant_form qf.c)
    | AFexists qf -> TFexists (to_quant_form qf.c)
    | AFlet (vs, s, t, aaf) -> TFlet (vs, s, to_tterm 0 t, to_tform aaf)
    | AFnamed (n, aaf) -> TFnamed (n, to_tform aaf)
  in
  { Typed.c = c;
    Typed.annot = id }

and to_tform aaf = void_to_tform aaf.c aaf.id

and from_aaform_list = function
  | [] -> []
  | aaf::l ->
    if aaf.pruned then from_aaform_list l
    else
      let l = from_aaform_list l in
      try (to_tform aaf)::l
      with Failure s ->
        assert (String.compare s "Empty logic operation" = 0);
        l

let rec to_typed_decl td =
  let c = match td.c with
    | ATheory (loc, name, ext, decls) ->
      TTheory (loc, name, ext, to_typed_decls decls)
    | AAxiom (loc, s, ax_kd, af) ->
      let af = void_to_tform af td.id in
      TAxiom (loc, s, ax_kd, af)
    | ARewriting (loc, s, arwtl) ->
      let rwtl = List.fold_left (fun rwtl ar ->
	if ar.pruned then rwtl
	else { rwt_vars = ar.c.rwt_vars;
	       rwt_left = to_tterm ar.id ar.c.rwt_left;
	       rwt_right = to_tterm ar.id ar.c.rwt_right}::rwtl
      ) [] arwtl in
      TRewriting (loc, s, rwtl)
    | AGoal (loc, gs, s, aaf) -> TGoal (loc, gs, s, to_tform aaf)
    | ALogic (loc, ls, ty) -> TLogic (loc, ls, ty)
    | APredicate_def (loc, p, spptl, af) ->
      TPredicate_def (loc, p, spptl, void_to_tform af td.id)
    | AFunction_def (loc, f, spptl, ty, af) ->
      TFunction_def (loc, f, spptl, ty, void_to_tform af td.id)
    | ATypeDecl (loc, ls, s, lc) -> TTypeDecl (loc, ls, s, lc)
  in
  { Typed.c = c;
    Typed.annot = td.id }

and to_typed_decls = function
  | [] -> []
  | atd::l ->
    if atd.pruned then to_typed_decls l
    else (to_typed_decl atd)::(to_typed_decls l)

let rec to_ast = function
  | [] -> []
  | (atd, _)::l ->
    if atd.pruned then to_ast l
    else (to_typed_decl atd)::(to_ast l)


let rec add_aterm_at (buffer:sbuffer) tags iter
    {at_desc = at_desc; at_ty = at_ty } =
  add_at_desc_at buffer tags iter at_desc

and add_aterm (buffer:sbuffer) tags tt =
  add_aterm_at buffer tags buffer#end_iter tt

and add_aterm_list_at (buffer:sbuffer) tags iter sep =
  function
    | [] -> ()
    | [at] -> add_aterm_at buffer tags iter at;
    | at::l ->
      add_aterm_at buffer tags iter at;
      append_buf buffer ~iter ~tags sep;
      add_aterm_list_at buffer tags iter sep l

and add_aaterm_at (buffer:sbuffer) tags iter at =
  at.line <- iter#line;
  add_aterm_at buffer (at.tag::at.ptag::tags) iter at.c

and add_aaterm (buffer:sbuffer) tags at =
  at.line <- buffer#line_count;
  add_aaterm_at buffer tags buffer#end_iter at

and add_aaterm_list_at (buffer:sbuffer) tags
    ?(multi_line=false) ?(offset=0) iter sep =
  function
    | [] -> ()
    | [at] -> add_aaterm_at buffer tags iter at;
    | at::l ->
      add_aaterm_at buffer tags iter at;
      append_buf buffer ~iter ~tags sep;
      if multi_line then begin
        append_buf buffer ~iter "\n";
        append_indentation buffer ~iter offset;
      end;
      add_aaterm_list_at buffer tags ~multi_line ~offset iter sep l

and add_aaterm_list (buffer:sbuffer) tags ?(multi_line = false) sep atl =
  let offset = buffer#end_iter#line_offset in
  add_aaterm_list_at buffer tags ~multi_line ~offset buffer#end_iter sep atl

and add_arecord_at (buffer:sbuffer) tags iter =
  function
    | [] -> ()
    | [c, at] ->
      append_buf buffer ~iter ~tags (sprintf "%s = " (Hstring.view c));
      add_aterm_at buffer tags iter at;
    | (c, at)::l ->
      append_buf buffer ~iter ~tags (sprintf "%s = " (Hstring.view c));
      add_aterm_at buffer tags iter at;
      append_buf buffer ~iter ~tags "; ";
      add_arecord_at buffer tags iter l

and add_at_desc_at (buffer:sbuffer) tags iter at =
  (* let off1 = iter#offset in *)
  (* let off = off1 - (buffer#get_iter (`OFFSET off1))#line_offset in *)
  (* print_endline (sprintf "%d" off); *)
  (* let iter = buffer#get_iter (`OFFSET off1) in *)
  match at with
    | ATconst c ->
      append_buf buffer ~iter ~tags
	(sprintf "%s" (tconstant_to_string c))
    | ATvar s  ->
      append_buf buffer ~iter ~tags (sprintf "%s" (Symbols.to_string_clean s))
    | ATapp (s, atl)  ->
      append_buf buffer ~iter ~tags
	(sprintf "%s(" (Symbols.to_string_clean s));
      add_aterm_list_at buffer tags iter ", " atl;
      append_buf buffer ~iter ~tags ")"
    | ATinfix (t1, s, t2)  ->
      add_aterm_at buffer tags iter t1;
      append_buf buffer ~iter ~tags
	(sprintf " %s " (Symbols.to_string_clean s));
      add_aterm_at buffer tags iter t2
    | ATprefix (s, t) ->
      append_buf buffer ~iter ~tags
	(sprintf "%s " (Symbols.to_string_clean s));
      add_aterm_at buffer tags iter t
    | ATget (t1, t2) ->
      add_aterm_at buffer tags iter t1;
      append_buf buffer ~iter ~tags "[";
      add_aterm_at buffer tags iter t2;
      append_buf buffer ~iter ~tags "]"
    | ATset (t1, t2, t3) ->
      add_aterm_at buffer tags iter t1;
      append_buf buffer ~iter ~tags "[";
      add_aterm_at buffer tags iter t2;
      append_buf buffer ~iter ~tags "<-";
      add_aterm_at buffer tags iter t3;
      append_buf buffer ~iter ~tags "]"
    | ATextract (t1, t2, t3) ->
      add_aterm_at buffer tags iter t1;
      append_buf buffer ~iter ~tags "^{";
      add_aterm_at buffer tags iter t2;
      append_buf buffer ~iter ~tags ", ";
      add_aterm_at buffer tags iter t3;
      append_buf buffer ~iter ~tags "}"
    | ATconcat (t1, t2) ->
      add_aterm_at buffer tags iter t1;
      append_buf buffer ~iter ~tags "@";
      add_aterm_at buffer tags iter t2
    | ATlet (s, t1, t2) ->
      append_buf buffer ~iter ~tags
	(sprintf "let %s = " (Symbols.to_string_clean s));
      add_aterm_at buffer tags iter t1;
      append_buf buffer ~iter ~tags " in ";
      add_aterm_at buffer tags iter t2
    | ATdot (t, c) ->
      add_aterm_at buffer tags iter t;
      append_buf buffer ~iter ~tags (sprintf ".%s" (Hstring.view c))
    | ATrecord r ->
      append_buf buffer ~iter ~tags "{ ";
      add_arecord_at buffer tags iter r;
      append_buf buffer ~iter ~tags " }"
    | ATnamed (n, t) ->
      append_buf buffer ~iter ~tags (sprintf "%s: " (Hstring.view n));
      add_aterm_at buffer tags iter t

    | ATmapsTo (n, t) ->
      append_buf buffer ~iter ~tags (sprintf "%s |-> " (Hstring.view n));
      add_aterm_at buffer tags iter t

    | ATinInterval(t1, lb, t2, t3, ub) ->
      add_aterm_at buffer tags iter t1;
      append_buf buffer ~iter ~tags " in ";
      append_buf buffer ~iter ~tags (if lb then "]" else "[");
      add_aterm_at buffer tags iter t2;
      append_buf buffer ~iter ~tags " , ";
      add_aterm_at buffer tags iter t3;
      append_buf buffer ~iter ~tags (if ub then "[" else "]")

let add_aatom (buffer:sbuffer) indent tags aa =
  append_indent buffer indent;
  match aa with
    | AAtrue -> append_buf buffer ~tags "true"
    | AAfalse -> append_buf buffer ~tags "false"
    | AAeq atl -> add_aaterm_list buffer tags " = " atl
    | AAneq atl -> add_aaterm_list buffer tags " <> " atl
    | AAdistinct atl  ->
      append_buf buffer ~tags "distinct(";
      add_aaterm_list buffer tags ", " atl;
      append_buf buffer  ~tags ")"
    | AAle atl -> add_aaterm_list buffer tags " <= " atl
    | AAlt atl -> add_aaterm_list buffer tags " < " atl
    | AApred at -> add_aterm buffer tags at
    | AAbuilt (h, atl) ->
      add_aaterm_list buffer tags (" "^(Hstring.view h)^" ") atl

let add_oplogic (buffer:sbuffer) indent tags op =
  match op with
    | AOPand -> append_buf buffer ~tags "and "
    | AOPor -> append_buf buffer ~tags "or "
    | AOPimp  -> append_buf buffer ~tags "-> "
    | AOPnot -> append_buf buffer ~tags "not "
    | AOPif at ->
      append_buf buffer (String.make indent ' ');
      append_buf buffer ~tags "if ";
      add_aterm buffer tags at;
      append_buf buffer ~tags " then "
    | AOPiff -> append_buf buffer ~tags "<-> "

let add_rwt (buffer:sbuffer) indent tags r =
  let { rwt_vars = rv; rwt_left = rl; rwt_right = rr } = r.c in
  let tags = r.tag::r.ptag::tags in
  append_indent buffer indent;
  append_buf buffer ~tags "forall ";
  fprintf str_formatter "%a. " print_var_list rv;
  append_buf buffer ~tags (flush_str_formatter ());
  add_aterm buffer tags rl;
  append_buf buffer ~tags " = ";
  add_aterm buffer tags rr

let rec add_rwt_list (buffer:sbuffer) indent tags = function
  | [] -> ()
  | [r] -> add_rwt buffer indent tags r
  | r::l ->
    add_rwt buffer indent tags r;
    append_buf buffer ~tags ";";
    append_buf buffer "\n";
    add_rwt_list buffer indent tags l


let add_empty_triggers_error ({rstore = rstore} as errors) (buffer:sbuffer) =
  let row = rstore#append () in
  rstore#set ~row ~column:errors.rcol_icon `DIALOG_WARNING;
  rstore#set ~row ~column:errors.rcol_desc
    "Warning : Empty trigger, this lemma won't be instantiated.";
  rstore#set ~row ~column:errors.rcol_color "red";
  rstore#set ~row ~column:errors.rcol_type 1;
  rstore#set ~row ~column:errors.rcol_line buffer#line_count;
  errors.some <- true


let rec add_quant_form errors (buffer:sbuffer) indent offset tags qf =
  let offset = offset + indent_size in
  let {aqf_bvars = bv; aqf_upvars = uv; aqf_triggers = trs; aqf_form = aaf;
      aqf_hyp} =
    qf.c in
  fprintf str_formatter "%a " print_var_list bv;
  append_buf buffer ~tags (flush_str_formatter ());
  let ntags = qf.tag::qf.ptag::tags in
  let multi_line_triggers =
    List.length trs > 2 ||
    List.exists (fun (t,_) -> List.length t > 2) trs ||
    aqf_hyp != [] in
  append_buf buffer ~tags:ntags "[";
  if multi_line_triggers then begin
    append_buf buffer "\n";
    append_indent buffer (indent + 1);
  end;
  add_triggers errors buffer ntags (indent+1) multi_line_triggers trs;
  append_mark buffer qf.id;
  if multi_line_triggers then begin
    append_buf buffer "\n";
    append_indent buffer indent;
  end;
  append_buf buffer ~tags:ntags "]";
  add_qf_hyp errors buffer indent ~tags:ntags aqf_hyp;
  append_buf buffer ~tags:ntags ".";
  append_buf buffer "\n";
  append_indentation buffer offset;
  add_aaform errors buffer (indent+1) tags aaf

and add_triggers errors (buffer:sbuffer) tags indent multi_line triggers =
  let rec add_triggers_aux  = function
    | [] -> ()
    | [atl, b] -> add_aaterm_list buffer tags ~multi_line ", " atl
    | (atl, b)::l ->
      add_aaterm_list buffer tags ~multi_line ", " atl;
      if multi_line then begin
        append_buf buffer "\n";
        append_indent buffer (indent-1);
      end else
        append_buf buffer ~tags " ";
      append_buf buffer ~tags "| ";
      add_triggers_aux l
  in
  if triggers == [] then add_empty_triggers_error errors buffer
  else add_triggers_aux triggers

and add_qf_hyp errors (buffer:sbuffer) indent ~tags aqf_hyp =
  let rec add_hyp_aux = function
    | [] -> ()
    | [aaf] -> add_aaform errors buffer (indent+1) tags aaf
    | aaf :: l ->
      add_aaform errors buffer (indent+1) tags aaf;
      append_buf buffer ~tags ",";
      append_buf buffer "\n";
      append_indent buffer (indent+1);
      add_hyp_aux l
  in
  if aqf_hyp != [] then begin
    append_buf buffer ~tags "{";
    append_buf buffer "\n";
    append_indent buffer (indent+1);
    add_hyp_aux aqf_hyp;
    append_buf buffer "\n";
    append_indent buffer indent;
    append_buf buffer ~tags "}"
  end

and add_aform errors (buffer:sbuffer) indent tags
    ?parent_op ?(paren=false) aform =
  match aform with
    | AFatom a -> add_aatom buffer 0 tags a
    | AFop (op, afl) ->
      add_aaform_list errors buffer indent tags ?parent_op op afl
    | AFforall qf ->
      let offset = buffer#end_iter#line_offset in
      append_buf buffer ~tags "forall ";
      add_quant_form errors buffer indent offset tags qf
    | AFexists qf ->
      let offset = buffer#end_iter#line_offset in
      append_buf buffer ~tags "exists ";
      add_quant_form errors buffer indent offset tags qf
    | AFlet (vs, s, t, aaf) ->
      append_buf buffer ~tags
	(sprintf "let %s = " (Symbols.to_string_clean s));
      add_aterm buffer tags t;
      append_buf buffer ~tags " in";
      append_buf buffer "\n";
      append_indent buffer indent;
      add_aaform errors buffer (indent) tags aaf
    | AFnamed (n, aaf) ->
      append_buf buffer ~tags (sprintf "%s: " (Hstring.view n));
      add_aform errors buffer indent tags ?parent_op aaf.c


and add_aaform_list
    errors (buffer:sbuffer) indent tags ?parent_op op l =
  if l == [] then ()
  else begin
    (* add_aaform buffer indent tags (List.hd l); *)
    add_aaform_list_aux errors buffer indent tags ?parent_op op l
  end

and add_aaform_list_aux
    errors (buffer:sbuffer) indent tags ?parent_op op =
  function
    | [] -> ()
    | [af] ->
      (* append_buf buffer ~tags "("; *)
      (* let offset = buffer#end_iter#line_offset in *)
      add_oplogic buffer indent tags op;
      add_aaform errors buffer indent tags ~parent_op:op af;
      (* append_buf buffer ~tags ")"; *)
    | af1::af2::l ->
      let paren = match parent_op, op with
          | None, _ -> false
          (* | Some AOPor, AOPand *)
          | Some AOPor, AOPor
          | Some AOPand, AOPand
          | Some (AOPimp | AOPiff), (AOPor | AOPand)
          | Some (AOPif _), (AOPor | AOPand | AOPimp | AOPiff) -> false
          | _ -> true
      in
      if paren then append_buf buffer ~tags "(";
      let offset = buffer#end_iter#line_offset in
      add_aaform errors buffer indent tags ~parent_op:op af1;
      if buffer#end_iter#line_offset >= max_indent then begin
        append_buf buffer "\n";
        append_indentation buffer offset;
      end else
        append_buf buffer " ";
      add_oplogic buffer indent tags op;
      add_aaform errors buffer (indent+1) tags ~parent_op:op af2;
      add_aaform_list errors buffer (indent+1) tags ~parent_op:op op l;
      if paren then append_buf buffer ~tags ")";
(* | af::l -> *)
(*     append_buf buffer "\n"; *)
(*     append_indent buffer indent; *)
(*     add_oplogic buffer indent tags op; *)
(*     add_aaform buffer indent tags af; *)
(*     add_aaform_list buffer (indent+1) tags op l *)


and add_aaform errors (buffer:sbuffer) indent tags ?parent_op
    ({c = af; tag = tag; ptag = ptag} as aaf) =
  aaf.line <- buffer#line_count;
  add_aform errors buffer indent (tag::ptag::tags) ?parent_op af

let rec add_atyped_decl errors (buffer:sbuffer) ?(indent=0) ?(tags=[]) d =
  if indent <> 0 then append_indent buffer indent;
  match d.c with
    | ATheory (loc, name, ext, l) ->
      fprintf str_formatter "theory %s extends %s =" name
        (Typed.string_of_th_ext ext);
      let ntags = d.tag :: d.ptag :: tags in
      append_buf buffer ~tags:ntags (flush_str_formatter());
      append_buf buffer "\n\n";
      List.iter
        (add_atyped_decl errors buffer ~indent:(indent+1) ~tags:ntags) l;
      append_buf buffer "\n";
      append_buf buffer ~tags "end";
      append_buf buffer "\n\n";
    | AAxiom (loc, s, ax_kd, af) ->
      let keyword =
	if String.length s > 0 &&
             (s.[0] == '_'  || s.[0] == '@')
	then "hypothesis"
        else match ax_kd with
        | Default -> "axiom"
        | Propagator ->
          Format.eprintf "[warning] may become 'propagator' in the future@.";
          "axiom"
      in
      let ntags = d.tag :: d.ptag :: tags in
      append_buf buffer ~tags:ntags (sprintf "%s %s :" keyword s);
      append_buf buffer "\n";
      d.line <- buffer#line_count;
      append_indent buffer (indent+1);
      add_aform errors buffer (indent+1) ntags af;
      append_buf buffer "\n\n"

    | ARewriting (loc, s, arwtl) ->
      let tags = d.tag :: d.ptag :: tags in
      append_buf buffer ~tags (sprintf "rewriting %s :" s);
      append_buf buffer "\n";
      d.line <- buffer#line_count;
      add_rwt_list buffer 1 tags arwtl;
      append_buf buffer "\n\n"

    | AGoal (loc, gs, s, aaf) ->
      let negate_aaform aaform =
        match aaform.c with
        | AFop (AOPnot, [aaf]) -> aaf.c
        | _ -> AFop (AOPnot, [aaform])
      in
      let goal_str =
	match gs with Thm -> "goal" | Check -> "check" | Cut -> "cut" in
      let tags = d.tag :: d.ptag :: tags in
      append_buf buffer ~tags (sprintf "%s %s :" goal_str s);
      append_buf buffer "\n";
      d.line <- buffer#line_count;
      append_indent buffer (indent+1);
      add_aform errors buffer (indent+1) tags (negate_aaform aaf);
      append_buf buffer "\n\n"

    | ALogic (loc, ls, ty) ->
      fprintf str_formatter
	"logic %a : %a" print_string_list ls print_plogic_type ty;
      d.line <- buffer#line_count;
      let tags = d.tag :: d.ptag :: tags in
      append_buf buffer ~tags (flush_str_formatter());
      append_buf buffer "\n\n"

    | APredicate_def (loc, p, spptl, af) ->
      fprintf str_formatter "predicate %s %a =" p print_pred_type_list spptl;
      let tags = d.tag :: d.ptag :: tags in
      append_buf buffer ~tags (flush_str_formatter());
      append_buf buffer "\n";
      d.line <- buffer#line_count;
      append_indent buffer (indent+1);
      add_aform errors buffer (indent+1) tags af;
      append_buf buffer "\n\n"

    | AFunction_def (loc, f, spptl, ty, af) ->
      fprintf str_formatter "function %s (%a) : %a =" f
	print_string_ppure_type_list spptl print_ppure_type ty;
      let tags = d.tag :: d.ptag :: tags in
      append_buf buffer ~tags (flush_str_formatter());
      append_buf buffer "\n";
      d.line <- buffer#line_count;
      append_indent buffer (indent+1);
      add_aform errors buffer (indent+1) tags af;
      append_buf buffer "\n\n"

    | ATypeDecl (loc, ls, s, Abstract) ->
      fprintf str_formatter "type %a %s" print_astring_list ls s;
      d.line <- buffer#line_count;
      append_buf buffer ~tags:(d.tag :: d.ptag :: tags) (flush_str_formatter());
      append_buf buffer "\n\n"

    | ATypeDecl (loc, ls, s, Enum lc) ->
      fprintf str_formatter "type %a %s = %a"
	print_astring_list ls s (print_string_sep " | ") lc;
      d.line <- buffer#line_count;
      append_buf buffer ~tags:(d.tag :: d.ptag :: tags) (flush_str_formatter());
      append_buf buffer "\n\n"

    | ATypeDecl (loc, ls, s, Record rt) ->
      fprintf str_formatter "type %a %s = { %a }"
	print_astring_list ls s	print_record_type rt;
      d.line <- buffer#line_count;
      append_buf buffer ~tags:(d.tag :: d.ptag :: tags) (flush_str_formatter());
      append_buf buffer "\n\n"

(* Remove introduced logic declarations for type constructors
 (for printing) *)
let rec filter_dummy_logics acc = function
  | [] -> List.rev acc
  | [td] -> List.rev (td :: acc)
  | ({ c = ALogic (_, _, PFunction ([], PPTexternal ([], t, _))) }, _) ::
    ((({ c = ATypeDecl (_, _, s, Enum _) }, _) :: _) as r)
    (* when String.equal t s  *) ->
    filter_dummy_logics acc r
  | td :: r -> filter_dummy_logics (td :: acc) r

let add_to_buffer errors (buffer:sbuffer) annoted_ast =
  List.iter (fun (t, _) -> add_atyped_decl errors buffer t)
    (filter_dummy_logics [] annoted_ast);
  commit_tags_buffer buffer






let rec isin_aterm sl { at_desc = at_desc } =
  match at_desc with
    | ATconst _ -> false
    | ATvar sy ->
      List.mem (Symbols.to_string_clean sy) sl
    | ATapp (sy, atl) ->
      List.mem (Symbols.to_string_clean sy) sl || isin_aterm_list sl atl
    | ATinfix (t1, _, t2) | ATget (t1,t2)
    | ATconcat (t1, t2) | ATlet (_, t1, t2) ->
      isin_aterm sl t1 || isin_aterm sl t2
    | ATdot (t, _ ) | ATprefix (_,t) | ATnamed (_, t)
    | ATmapsTo (_, t) -> isin_aterm sl t
    | ATset (t1, t2, t3) | ATextract (t1, t2, t3)
    | ATinInterval(t1, _, t2, t3, _) ->
      isin_aterm sl t1 || isin_aterm sl t2 || isin_aterm sl t3
    | ATrecord rt -> let atl = List.map snd rt in isin_aterm_list sl atl

and isin_aterm_list sl atl =
  List.fold_left
    (fun is at -> is || isin_aterm sl at
    ) false atl

and findtags_aaterm sl aat acc =
  match aat.c.at_desc with
    | ATconst _ -> acc
    | ATvar sy ->
      if List.mem (Symbols.to_string_clean sy) sl then aat.tag::acc else acc
    | ATapp (sy, atl) ->
      if List.mem (Symbols.to_string_clean sy) sl || isin_aterm_list sl atl
      then aat.tag::acc else acc
    | ATinfix (t1, _, t2) | ATget (t1,t2)
    | ATconcat (t1, t2) | ATlet (_, t1, t2) ->
      if isin_aterm sl t1 || isin_aterm sl t2 then aat.tag::acc else acc
    | ATdot (t, _) | ATprefix (_,t) | ATnamed (_, t)
    | ATmapsTo (_, t) ->
      if isin_aterm sl t then aat.tag::acc else acc
    | ATset (t1, t2, t3) | ATextract (t1, t2, t3)
    | ATinInterval(t1, _, t2, t3, _)->
      if isin_aterm sl t1 || isin_aterm sl t2 || isin_aterm sl t3
      then aat.tag::acc else acc
    | ATrecord r ->
      let atl = List.map snd r in
      if isin_aterm_list sl atl then aat.tag::acc else acc

and findtags_aaterm_list sl aatl acc =
  List.fold_left
    (fun acc aat ->
      findtags_aaterm sl aat acc
    ) acc aatl

let findtags_aatom sl aa acc =
  match aa with
    | AAtrue
    | AAfalse -> acc

    | AAeq atl
    | AAneq atl
    | AAdistinct atl
    | AAle atl
    | AAlt atl
    | AAbuilt (_, atl) -> findtags_aaterm_list sl atl acc

    | AApred at -> acc


let rec findtags_quant_form
    sl {aqf_triggers = trs; aqf_form = aaf ; aqf_hyp } acc =
  let acc = findtags_triggers sl trs acc in
  let acc = findtags_aaform_list sl aqf_hyp acc in
  findtags_aaform sl aaf acc

and findtags_triggers sl trs acc =
  List.fold_left
    (fun acc (aatl, b) ->
      findtags_aaterm_list sl aatl acc
    ) acc trs

and findtags_aform sl aform acc =
  match aform with
    | AFatom a -> findtags_aatom sl a acc
    | AFop (op, afl) -> findtags_aaform_list sl afl acc
    | AFforall qf
    | AFexists qf -> findtags_quant_form sl qf.c acc
    | AFlet (vs, sy, t, aaf) ->
        (* let acc = findtags_aterm sl t acc in *)
      let s = Symbols.to_string_clean sy in
      let sl =
        List.fold_left
          (fun l s' -> if Pervasives.(=) s' s then l else s'::l) [] sl
      in
      findtags_aform sl aaf.c acc
    | AFnamed (_, aaf) ->
      findtags_aform sl aaf.c acc

and findtags_aaform_list sl aafl acc =
  List.fold_left
    (fun acc aaf -> findtags_aaform sl aaf acc
    ) acc aafl

and findtags_aaform sl aaf acc =
  match aaf.c with
    | AFatom (AApred at) when isin_aterm sl at -> aaf.tag::acc
    | _ -> findtags_aform sl aaf.c acc

let rec findtags_atyped_delc sl td acc =
  match td.c with
    | ATheory (_, _, _, l) ->
      List.fold_left (fun acc td -> findtags_atyped_delc sl td acc)acc l
    | AAxiom (_, _, _, af)
    | APredicate_def (_, _, _, af)
    | AFunction_def (_, _, _, _, af) ->
      let aaf = (* incorrect annotations : to change *)
        { c = af;
          tag = td.tag;
          pruned = td.pruned;
          ptag = td.ptag;
          id = td.id;
          buf = td.buf;
          line = td.line;
          polarity = td.polarity;
        } in
      findtags_aaform sl aaf acc
    | ARewriting (_, _, rwtl) -> acc
    | AGoal (_, _, _, aaf) ->
      findtags_aform sl aaf.c acc
    | ALogic _
    | ATypeDecl _ -> acc

let findtags sl l =
  List.fold_left
    (fun acc (td, _) -> findtags_atyped_delc sl td acc
    ) [] l

let findtags_using r l =
  match r with
    | ATheory (_, _, _, decls) ->
      fprintf fmt "7 !@.";
      assert false
    | AAxiom _
    | ARewriting _
    | AGoal _
    | ATypeDecl _ -> []

    | ALogic (_, sl, _) -> findtags sl l

    | APredicate_def (_, s, _, _)
    | AFunction_def (_, s, _, _, _) -> findtags [s] l

let rec listsymbols at acc =
  match at.at_desc with
    | ATconst _ -> acc
    | ATvar sy -> (Symbols.to_string_clean sy)::acc
    | ATapp (sy, atl) ->
      List.fold_left (fun acc at -> listsymbols at acc)
	((Symbols.to_string_clean sy)::acc) atl
    | ATinfix (t1, _, t2) | ATget (t1,t2)
    | ATconcat (t1, t2) | ATlet (_, t1, t2) ->
      listsymbols t1 (listsymbols t2 acc)
    | ATdot (t, _) | ATprefix (_,t) | ATnamed (_, t) -> listsymbols t acc
    | ATset (t1, t2, t3) | ATextract (t1, t2, t3)  ->
      listsymbols t1 (listsymbols t2 (listsymbols t3 acc))
    | ATrecord r ->
      List.fold_left (fun acc (_, at) -> listsymbols at acc) acc r

    | ATmapsTo (hs, t) -> listsymbols t acc

    | ATinInterval(e, lb, i, j, ub) ->
      List.fold_left (fun acc at -> listsymbols at acc) acc [e; i; j]

and listsymbols_aform af acc =
  match af with
  | AFatom a -> listsymbols_atom a acc
  | AFop (_, aafl) ->
    List.fold_left (fun acc aaf -> listsymbols_aform aaf.c acc) acc aafl
  | AFforall aqf | AFexists aqf ->
    let acc = listsymbols_aform aqf.c.aqf_form.c acc in
    let acc =
      List.fold_left (fun acc hyp -> listsymbols_aform hyp.c acc)
        acc aqf.c.aqf_hyp in
    List.fold_left (fun acc (aatl ,_) ->
        List.fold_left (fun acc aat -> listsymbols aat.c acc) acc aatl
      ) acc aqf.c.aqf_triggers
  | AFlet (_, _, at, aaf) -> listsymbols_aform aaf.c (listsymbols at acc)
  | AFnamed (_, aaf) -> listsymbols_aform aaf.c acc

and listsymbols_atom a acc =
  match a with
  | AAtrue | AAfalse -> acc
  | AAeq aatl | AAneq aatl | AAdistinct aatl
  | AAle aatl | AAlt aatl | AAbuilt (_, aatl) ->
    List.fold_left (fun acc aat -> listsymbols aat.c acc) acc aatl
  | AApred at -> listsymbols at acc


let rec listsymbols_adecl ad =
  match ad with
  | ATheory (_, _, _, l) ->
    List.fold_left
      (fun acc ad -> List.rev_append (listsymbols_adecl ad.c) acc) [] l
  | AAxiom (_,_, _, af)
  | APredicate_def (_, _, _, af)
  | AFunction_def (_, _, _, _, af) -> listsymbols_aform af []
  | AGoal (_, _, _, aaf) -> listsymbols_aform aaf.c []
  | ATypeDecl _ | ALogic _ | ARewriting _ -> []


let findtags_atyped_delc_dep sl td acc =
  match td.c with
    | ALogic (_, ls, _) ->
      let ne = List.fold_left (fun ne s -> ne || List.mem s sl) false ls in
      if ne then td.tag::acc else acc
    | APredicate_def (_, p, _, _) when List.mem p sl -> td.tag::acc
    | AFunction_def (_, f, _, _, _) when List.mem f sl -> td.tag::acc
    | _ -> acc


let findtags_dep at l =
  let sl = listsymbols at [] in
  List.fold_left (fun acc (td, _) -> findtags_atyped_delc_dep sl td acc) [] l


let findtags_dep_aform af l =
  let sl = listsymbols_aform af [] in
  List.fold_left (fun acc (td, _) -> findtags_atyped_delc_dep sl td acc) [] l


let findtags_dep_adecl ad l =
  let sl = listsymbols_adecl ad in
  List.fold_left (fun acc (td, _) -> findtags_atyped_delc_dep sl td acc) [] l


let rec findproof_aform ids af acc depth found =
  match af with
    | AFatom at -> acc, found
    | AFop ((AOPand), aafl) ->
      List.fold_left
    	(fun (acc, found) aaf -> findproof_aaform ids aaf acc depth found)
    	(acc,found) aafl
    | AFop (_, aafl) ->
      List.fold_left
	(fun (acc, found) aaf ->
	  findproof_aaform ids aaf acc depth found)
	(acc,found) aafl
    | AFforall aaqf | AFexists aaqf ->
      let acc, found =
	try
	  let m = Explanation.MI.find aaqf.id ids in
	  MTag.add aaqf.ptag m acc, true
	with Not_found -> acc, found
      in
      let acc, found =
        List.fold_left (fun (acc, found) aaf ->
	  findproof_aaform ids aaf acc depth found)
	(acc,found) aaqf.c.aqf_hyp in
      findproof_aaform ids aaqf.c.aqf_form acc depth found
    | AFlet (_,_,_, aaf) | AFnamed (_, aaf) ->
      findproof_aaform ids aaf acc depth found

and findproof_aaform ids aaf acc depth found =
  let acc, found =
    try
      let m = Explanation.MI.find aaf.id ids in
      MTag.add aaf.ptag m acc, true
    with Not_found -> acc, found
  in
  findproof_aform ids aaf.c acc (depth) found

let rec findproof_atyped_decl ids td (ax,acc) =
  let acc =
    try
      let m = Explanation.MI.find td.id ids in
      MTag.add td.ptag m acc
    with Not_found -> acc
  in
  match td.c with
    | ATheory (_, _, _, l) ->
      List.fold_left
        (fun accu td -> findproof_atyped_decl ids td accu) (ax, acc) l

    | ARewriting (_,_, arwtl) -> assert false

    | ALogic _ | ATypeDecl _ -> ax,acc

    | APredicate_def (_,_,_, af)
    | AFunction_def (_,_,_,_, af)
    | AAxiom (_, _, _, af) ->
      let acc, found = findproof_aform ids af acc 1 false in
      if found then td.ptag::ax, acc else ax,acc

    | AGoal (_,_,_, aaf) ->
      let acc, found = findproof_aaform ids aaf acc 1 false in
      if found then td.ptag::ax, acc else ax,acc

let findtags_proof expl l =
  let ids = Explanation.literals_ids_of expl in
  List.fold_left (fun acc (td, _) ->
    findproof_atyped_decl ids td acc) ([], MTag.empty) l


exception FoundLine of int * GText.tag

let rec find_line_id_aform id af =
  match af with
    | AFatom at -> ()
    | AFop (_, aafl) ->
      List.iter (find_line_id_aaform id) aafl
    | AFforall aaqf | AFexists aaqf ->
      if aaqf.id = id then raise (FoundLine (aaqf.line, aaqf.tag))
      else find_line_id_aaform id aaqf.c.aqf_form
    | AFlet (_,_,_, aaf) | AFnamed (_, aaf) ->
      find_line_id_aaform id aaf

and find_line_id_aaform id aaf =
  if aaf.id = id then raise (FoundLine (aaf.line, aaf.tag))
  else find_line_id_aform id aaf.c

let rec find_line_id_atyped_decl id td =
  if td.id < id then ()
  else if td.id = id then raise (FoundLine (td.line, td.tag))
  else match td.c with
    | ATheory (_, _, _, l) ->
      List.iter (find_line_id_atyped_decl id) l
    | ARewriting (_,_, _)
    | ALogic _ | ATypeDecl _  -> ()

    | APredicate_def (_,_,_, af)
    | AFunction_def (_,_,_,_, af)
    | AAxiom (_, _, _, af) ->
      find_line_id_aform id af

    | AGoal (_,_,_, aaf) ->
      find_line_id_aaform id aaf

let find_line id l =
  try
    List.iter (fun (d, _) -> find_line_id_atyped_decl id d) l;
    raise Not_found
  with FoundLine (line, tag) -> line, tag



exception Foundannot of annoted_node



let findbyid_aaterm id aat =
  if aat.id = id then raise (Foundannot (AT aat))

(*   else findbyid_atdesc id aat.c.at_desc *)

(* and findbyid_atdesc id = function *)
(*   | ATconst _ | ATvar _ -> () *)
(*   | ATapp (s, atl) -> List.iter (findbyid_aaterm id) atl *)
(*   | ATinfix (t1, _, t2) | ATget (t1,t2) *)
(*   | ATconcat (t1, t2) | ATlet (_, t1, t2) -> *)
(*     findbyid_aaterm id t1; *)
(*     findbyid_aaterm id t2 *)
(*   | ATdot (t, _) | ATprefix (_,t) | ATnamed (_, t) ->
     findbyid_aaterm id t *)
(*   | ATset (t1, t2, t3) | ATextract (t1, t2, t3)  -> *)
(*     findbyid_aaterm id t1; *)
(*     findbyid_aaterm id t2; *)
(*     findbyid_aaterm id t3 *)
(*   | ATrecord r ->  *)
(*     let atl = List.map snd r in List.iter (findbyid_aaterm id) atl     *)

let findbyid_aatom id = function
  | AAtrue
  | AAfalse -> ()

  | AAeq atl
  | AAneq atl
  | AAdistinct atl
  | AAle atl
  | AAlt atl
  | AAbuilt (_, atl) -> List.iter (findbyid_aaterm id) atl

  | AApred at -> ()

let rec findbyid_aform id af =
  match af with
    | AFatom aat -> findbyid_aatom id aat
    | AFop (_, aafl) ->
      List.iter (findbyid_aaform id) aafl
    | AFforall aaqf | AFexists aaqf ->
      List.iter
        (fun (l,_) -> List.iter (findbyid_aaterm id) l) aaqf.c.aqf_triggers;
      List.iter (findbyid_aaform id) aaqf.c.aqf_hyp;
      if aaqf.id = id then raise (Foundannot (QF aaqf))
      else findbyid_aaform id aaqf.c.aqf_form
    | AFlet (_,_,_, aaf) | AFnamed (_, aaf) ->
      findbyid_aaform id aaf

and findbyid_aaform id aaf =
  if aaf.id = id then raise (Foundannot (AF (aaf, None)))
  else findbyid_aform id aaf.c

let findbyid_atyped_decl  stop_decl id (td, tyenv) =
  if td.id < id then ()
  else if td.id = id then raise (Foundannot (AD (td, tyenv)))
  else if stop_decl then raise (Foundannot (AD (td, tyenv)))
  else match td.c with
    | ATheory (_, _, _, l) ->
      fprintf fmt "11 !@.";
      assert false
    | ARewriting (_,_, _)
    | ALogic _ | ATypeDecl _  -> ()

    | APredicate_def (_,_,_, af)
    | AFunction_def (_,_,_,_, af)
    | AAxiom (_, _, _, af) ->
      findbyid_aform id af

    | AGoal (_,_,_, aaf) ->
      findbyid_aaform id aaf

let findbyid_aux stop_decl id l =
  try
    List.iter (findbyid_atyped_decl stop_decl id) l;
    raise Not_found
  with Foundannot a -> a

let findbyid = findbyid_aux false

let findbyid_decl = findbyid_aux true

let compute_resulting_ids =
  let rec aux acc td =
    match td.c with
    | ARewriting (_,_, _) -> acc
    | ALogic (_, names, _) -> (List.map (fun n -> n, td.id) names)@acc
    | ATypeDecl (_, _, name, _)
    | APredicate_def (_, name, _, _)
    | AFunction_def (_, name, _, _, _)
    | AAxiom (_, name, _, _)
    | AGoal (_,_, name, _) -> (name, td.id)::acc
    | ATheory (_, _, _, l) ->
      List.fold_left aux acc l
  in
  fun lp -> List.fold_left (fun acc (td, _) -> aux acc td) [] lp


(* remove optional arguement in interface *)
let add_aaform errors buffer indent tags aaf =
  add_aaform errors buffer indent tags aaf
