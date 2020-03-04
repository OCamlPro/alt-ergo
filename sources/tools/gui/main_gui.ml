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
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open AltErgoLib
open AltErgoParsers
open Typed
open Commands
open Gui_config
open Annoted_ast
open Connected_ast

open Format
open Options

(* done here to initialize options,
   before the instantiations of functors *)
let () = Options.parse_cmdline_arguments ()

module SatCont = (val (Sat_solver.get_current ()) : Sat_solver_sig.SatContainer)

module TH =
  (val
    (if Options.no_theory() then (module Theory.Main_Empty : Theory.S)
     else (module Theory.Main_Default : Theory.S)) : Theory.S )

module SAT = SatCont.Make(TH)

module FE = Frontend.Make(SAT)

(* type search_bar = { *)
(*   sbar: GButton.toolbar; *)
(*   sbox: GPack.box; *)
(*   sentry: GEdit.entry; *)
(*   button_forw: GButton.button; *)
(*   button_back: GButton.button; *)
(*   found_all_tag: GText.tag; *)
(*   found_tag: GText.tag; *)
(* } *)

(* type page_toolbar = { *)
(*   pbox: GPack.box; *)
(*   pbar: GButton.toolbar; *)
(*   button_context: GButton.button; *)
(*   button_run: GButton.button; *)
(*   button_stop: GButton.button; *)
(*   result_box: GPack.box; *)
(*   result_image: GMisc.image; *)
(*   result_label: GMisc.label; *)
(*   button_clean: GButton.button; *)
(*   search_bar: search_bar; *)
(* } *)

(* type page = { *)
(*   tab_label: GMisc.label; *)
(*   page_nb: int; *)
(*   event_box: GBin.event_box; *)
(*   toolbar: page_toolbar; *)
(*   statusbar: GMisc.statusbar; *)
(*   st_ctx : GMisc.statusbar_context; *)

(*   main_view: GSourceView2.source_view; *)
(*   main_buffer: GSourceView2.source_buffer; *)
(*   inst_view: GSourceView2.source_view; *)
(*   inst_buffer: GSourceView2.source_buffer; *)

(*   error_model: error_model; *)
(*   inst_model: inst_model; *)
(*   timers_model: timers_model; *)

(*   mutable ast : (atyped_decl annoted * Why_typing.env) list; *)
(*   dep : (atyped_decl annoted list * atyped_decl annoted list) MDep.t; *)

(*   thread: Thread.t option; *)

(*   mutable ctrl_toggled : bool; *)
(*   mutable last_tag : GText.tag; *)
(*   mutable search_tags : GText.tag list; *)
(*   mutable proof_tags : GText.tag list; *)
(*   mutable proof_toptags : GText.tag list; *)
(*   mutable start_select : int option; *)
(*   mutable stop_select : int option; *)

(*   actions : Gui_session.action Stack.t; *)
(*   saved_actions : Gui_session.action Stack.t; *)
(*   resulting_ids : (string * int) list; *)
(* } *)

(* type gui = { *)
(*   source_language: GSourceView2.source_language option; *)
(*   scheme: GSourceView2.source_style_scheme option; *)
(*   note_search: (int, GEdit.entry * (unit -> unit)) Hashtbl.t; *)

(*   w: GWindow.window; *)
(*   menubar: GMenu.menu_shell; *)
(*   notebook: GPack.notebook; *)

(*   mutable pages: page list; *)
(* } *)


let inf = Glib.Utf8.from_unichar 8734

(* GTK *)

let () =
  try
    let _ = GMain.init () in ()
  with Gtk.Error s -> eprintf "%s@." s

let () =
  Sys.set_signal Sys.sigint
    (Sys.Signal_handle
       (fun _ -> print_endline "User wants me to stop."; exit 1))


let save_session envs =
  let session_cout =
    open_out_gen [Open_creat; Open_wronly; Open_binary] 0o640
      (get_session_file())
  in
  List.iter (fun env ->
      output_value session_cout env.resulting_ids;
      output_value session_cout env.actions)
    envs;
  close_out session_cout

let save_dialog cancel envs () =
  if List.exists
      (fun env -> Stdlib.(<>) env.actions env.saved_actions) envs then
    if List.exists
        (fun env -> not (Gui_session.safe_session env.actions)) envs then
      GToolbox.message_box
        ~title:"Unsafe session"
        ~icon:(GMisc.image ~stock:`DIALOG_ERROR  ~icon_size:`DIALOG ())
        ~ok:"OK"
        "Your current session is unsafe: satifiability is not preserved.\n\
         Please ensure you haven't performed any incorrect prunings before \
         saving."
    else
    if GToolbox.question_box
        ~title:"Save session" ~buttons:[cancel; "Save"]
        ~default:2 ~icon:(GMisc.image ~stock:`SAVE  ~icon_size:`DIALOG ())
        "Would you like to save the current session ?" = 2 then
      save_session envs

let quit envs () =
  Gui_config.write ();
  save_dialog "Quit" envs ();
  GMain.quit ()


let show_about () =
  let v = "Alt-Ergo" in
  let aw = GWindow.about_dialog ~name:v
      ~position:`CENTER
      ~authors:["Sylvain Conchon";
                "Évelyne Contejean";
                "Francois Bobot";
                "Mohamed Iguernlala";
                "Stephane Lescuyer";
                "Alain Mebsout"]
      ~copyright:"CNRS - INRIA - Université Paris Sud (2006-2013)\n\
                  OCamlPro (2013-2018)"
      ~license:"CeCILL-C"
      ~version:Version._version
      ~website:"http://alt-ergo.lri.fr\nhttp://alt-ergo.ocamlpro.com"
      ~title:v ()
  in
  ignore (aw#connect#response ~callback:(fun _ -> aw#destroy ()));
  ignore (aw#connect#close ~callback:(aw#destroy));
  aw#show ()

let pop_error ?(error=false) ~message () =
  let pop_w = GWindow.dialog
      ~title:(if error then "Error" else "Warning")
      ~allow_grow:true
      ~position:`CENTER
      ~width:400 ()
  in
  let bbox = GPack.button_box `HORIZONTAL ~border_width:5 ~layout:`END
      ~child_height:20 ~child_width:85 ~spacing:10
      ~packing:pop_w#action_area#add () in

  let button_ok = GButton.button ~packing:bbox#add () in
  let phbox = GPack.hbox ~packing:button_ok#add () in
  ignore(GMisc.image ~stock:`OK ~packing:phbox#add ());
  ignore(GMisc.label ~text:"OK" ~packing:phbox#add ());

  let hbox = GPack.hbox ~border_width:5 ~packing:pop_w#vbox#pack () in

  ignore(GMisc.image ~stock:(if error then `DIALOG_ERROR else `DIALOG_WARNING)
           ~icon_size:`DIALOG ~packing:hbox#pack ());
  ignore(GMisc.label ~text:message
           ~xalign:0. ~xpad:10 ~packing:hbox#add ());
  ignore(button_ok#connect#clicked ~callback: pop_w#destroy);
  pop_w#show ()


let pop_model sat_env () =
  let pop_w = GWindow.dialog
      ~title:"Model"
      ~allow_grow:true
      ~destroy_with_parent:true
      ~position:`CENTER
      ~width:400
      ~height:300 ()
  in

  let sw1 = GBin.scrolled_window
      ~vpolicy:`AUTOMATIC
      ~hpolicy:`AUTOMATIC
      ~packing:pop_w#vbox#add () in
  let buf1 = GSourceView2.source_buffer () in
  let tv1 = GSourceView2.source_view ~source_buffer:buf1 ~packing:(sw1#add)
      ~wrap_mode:`CHAR () in
  let _ = tv1#misc#modify_font monospace_font in
  let _ = tv1#set_editable false in
  fprintf str_formatter "%a" (SAT.print_model ~header:false) sat_env;
  let model_text = (flush_str_formatter()) in
  buf1#set_text model_text;
  pop_w#show ()



let compare_rows icol_number (model:#GTree.model) row1 row2 =
  let t1 = model#get ~row:row1 ~column:icol_number in
  let t2 = model#get ~row:row2 ~column:icol_number in
  Stdlib.compare t1 t2


let empty_inst_model () =
  let icols = new GTree.column_list in
  let icol_icon = icols#add GtkStock.conv in
  let icol_desc = icols#add Gobject.Data.string in
  let icol_number = icols#add Gobject.Data.int in
  let icol_limit = icols#add Gobject.Data.string in
  let icol_tag = icols#add Gobject.Data.int in
  let istore = GTree.list_store icols in
  istore#set_sort_func icol_number.GTree.index (compare_rows icol_number);
  istore#set_sort_func icol_desc.GTree.index (compare_rows icol_desc);
  istore#set_sort_column_id icol_number.GTree.index `DESCENDING;
  {
    h = Hashtbl.create 17;
    max = 0;
    icols = icols;
    icol_icon = icol_icon;
    icol_desc = icol_desc;
    icol_number = icol_number;
    icol_limit = icol_limit;
    icol_tag = icol_tag;
    istore = istore;
  }


let empty_timers_model (table:GPack.table) =
  let t =
    {
      timers = Timers.empty ();

      label_sat =
        GMisc.label ~text:"SAT" ~justify:`LEFT ~xalign:0.
          ~packing:(table#attach ~left:0 ~top:0) ();
      label_match =
        GMisc.label ~text:"Matching" ~justify:`LEFT ~xalign:0.
          ~packing:(table#attach ~left:0 ~top:1) ();
      label_cc =
        GMisc.label ~text:"CC(X)" ~justify:`LEFT ~xalign:0.
          ~packing:(table#attach ~left:0 ~top:2) ();
      label_arith =
        GMisc.label ~text:"Arith" ~justify:`LEFT ~xalign:0.
          ~packing:(table#attach ~left:0 ~top:3) ();
      label_arrays =
        GMisc.label ~text:"Arrays" ~justify:`LEFT~xalign:0.
          ~packing:(table#attach ~left:0 ~top:4) ();
      label_sum =
        GMisc.label ~text:"Sum" ~justify:`LEFT ~xalign:0.
          ~packing:(table#attach ~left:0 ~top:5) ();
      label_records =
        GMisc.label ~text:"Records" ~justify:`LEFT ~xalign:0.
          ~packing:(table#attach ~left:0 ~top:6) ();
      label_ac =
        GMisc.label ~text:"AC(X)" ~justify:`LEFT ~xalign:0.
          ~packing:(table#attach ~left:0 ~top:7) ();

      tl_sat =
        GMisc.label ~text:"0.000 s" ~justify:`RIGHT
          ~packing:(table#attach ~left:1 ~top:0) ();
      tl_match =
        GMisc.label ~text:"0.000 s" ~justify:`RIGHT
          ~packing:(table#attach ~left:1 ~top:1) ();
      tl_cc =
        GMisc.label ~text:"0.000 s" ~justify:`RIGHT
          ~packing:(table#attach ~left:1 ~top:2) ();
      tl_arith =
        GMisc.label ~text:"0.000 s" ~justify:`RIGHT
          ~packing:(table#attach ~left:1 ~top:3) ();
      tl_arrays =
        GMisc.label ~text:"0.000 s" ~justify:`RIGHT
          ~packing:(table#attach ~left:1 ~top:4) ();
      tl_sum =
        GMisc.label ~text:"0.000 s" ~justify:`RIGHT
          ~packing:(table#attach ~left:1 ~top:5) ();
      tl_records =
        GMisc.label ~text:"0.000 s" ~justify:`RIGHT
          ~packing:(table#attach ~left:1 ~top:6) ();
      tl_ac =
        GMisc.label ~text:"0.000 s" ~justify:`RIGHT
          ~packing:(table#attach ~left:1 ~top:7) ();

      pr_sat =
        GRange.progress_bar ~packing:(table#attach ~left:2 ~top:0
                                        ~expand:`X ~shrink:`BOTH) ();
      pr_match =
        GRange.progress_bar ~packing:(table#attach ~left:2 ~top:1
                                        ~expand:`X ~shrink:`BOTH) ();
      pr_cc =
        GRange.progress_bar ~packing:(table#attach ~left:2 ~top:2
                                        ~expand:`X ~shrink:`BOTH) ();
      pr_arith =
        GRange.progress_bar ~packing:(table#attach ~left:2 ~top:3
                                        ~expand:`X ~shrink:`BOTH) ();
      pr_arrays =
        GRange.progress_bar ~packing:(table#attach ~left:2 ~top:4
                                        ~expand:`X ~shrink:`BOTH) ();
      pr_sum =
        GRange.progress_bar ~packing:(table#attach ~left:2 ~top:5
                                        ~expand:`X ~shrink:`BOTH) ();
      pr_records =
        GRange.progress_bar ~packing:(table#attach ~left:2 ~top:6
                                        ~expand:`X ~shrink:`BOTH) ();
      pr_ac =
        GRange.progress_bar ~packing:(table#attach ~left:2 ~top:7
                                        ~expand:`X ~shrink:`BOTH) ();
    } in

  t.pr_sat#set_text " 0 %";
  t.pr_match#set_text  " 0 %";
  t.pr_cc#set_text " 0 %";
  t.pr_arith#set_text  " 0 %";
  t.pr_arrays#set_text  " 0 %";
  t.pr_sum#set_text  " 0 %";
  t.pr_records#set_text " 0 %";
  t.pr_ac#set_text  " 0 %";
  t


let refresh_timers t () =
  let tsat = Timers.get_sum t.timers Timers.M_Sat in
  let tmatch = Timers.get_sum t.timers Timers.M_Match in
  let tcc = Timers.get_sum t.timers Timers.M_CC in
  let tarith = Timers.get_sum t.timers Timers.M_Arith in
  let tarrays = Timers.get_sum t.timers Timers.M_Arrays in
  let tsum = Timers.get_sum t.timers Timers.M_Sum in
  let trecords = Timers.get_sum t.timers Timers.M_Records in
  let tac = Timers.get_sum t.timers Timers.M_AC in

  let total =
    tsat +. tmatch +. tcc +. tarith +. tarrays +. tsum +. trecords +. tac in

  let total = if Stdlib.(=) total 0. then 1. else total in

  t.tl_sat#set_text (sprintf "%3.2f s" tsat);
  t.tl_match#set_text (sprintf "%3.2f s" tmatch);
  t.tl_cc#set_text (sprintf "%3.2f s" tcc);
  t.tl_arith#set_text (sprintf "%3.2f s" tarith);
  t.tl_arrays#set_text (sprintf "%3.2f s" tarrays);
  t.tl_sum#set_text (sprintf "%3.2f s" tsum);
  t.tl_records#set_text (sprintf "%3.2f s" trecords);
  t.tl_ac#set_text (sprintf "%3.2f s" tac);

  t.pr_sat#set_fraction (tsat /. total);
  t.pr_sat#set_text (sprintf "%2.0f %%" (tsat *. 100. /. total));

  t.pr_match#set_fraction (tmatch /. total);
  t.pr_match#set_text (sprintf "%2.0f %%" (tmatch *. 100. /. total));

  t.pr_cc#set_fraction (tcc /. total);
  t.pr_cc#set_text (sprintf "%2.0f %%" (tcc *. 100. /. total));

  t.pr_arith#set_fraction (tarith /. total);
  t.pr_arith#set_text (sprintf "%2.0f %%" (tarith *. 100. /. total));

  t.pr_arrays#set_fraction (tarrays /. total);
  t.pr_arrays#set_text (sprintf "%2.0f %%" (tarrays *. 100. /. total));

  t.pr_sum#set_fraction (tsum /. total);
  t.pr_sum#set_text (sprintf "%2.0f %%" (tsum *. 100. /. total));

  t.pr_records#set_fraction (trecords /. total);
  t.pr_records#set_text (sprintf "%2.0f %%" (trecords *. 100. /. total));

  t.pr_ac#set_fraction (tac /. total);
  t.pr_ac#set_text (sprintf "%2.0f %%" (tac *. 100. /. total));

  true


let reset_timers timers_model =
  Timers.reset timers_model.timers;
  ignore (refresh_timers timers_model ())



let refresh_instances ({ istore; _ } as inst_model) () =
  Hashtbl.iter (fun id (r, n, name, limit) ->
      let row, upd_info =
        match !r with
        | Some row -> row, false
        | None ->
          let row = istore#append () in
          r := Some row;
          row, true in
      let nb = !n in
      inst_model.max <- max inst_model.max nb;
      if upd_info then begin
        istore#set ~row ~column:inst_model.icol_icon `INFO;
        istore#set ~row ~column:inst_model.icol_desc name;
        let slimit =
          if !limit >= 0 then string_of_int !limit
          else "∞" in
        istore#set ~row ~column:inst_model.icol_limit slimit;
      end;
      istore#set ~row ~column:inst_model.icol_number nb;
      istore#set ~row ~column:inst_model.icol_tag id
    ) inst_model.h;
  true


let add_inst ({ h; _ } as inst_model) orig =
  let id = Expr.id orig in
  let name =
    match Expr.form_view orig with
    | Expr.Lemma { Expr.name = n ; _ } when Stdlib.(<>) n "" -> n
    | Expr.Lemma _ | Expr.Unit _ | Expr.Clause _ | Expr.Literal _
    | Expr.Skolem _ | Expr.Let _ | Expr.Iff _ | Expr.Xor _ ->
      string_of_int id
    | Expr.Not_a_form -> assert false
  in
  let r, n, limit, to_add =
    try
      let r, n, _, limit = Hashtbl.find h id in
      r, n, limit, false
    with Not_found -> ref None, ref 0, ref (-1), true
  in
  if !limit <> -1 && !limit < !n + 1 then false
  else begin
    incr n;
    if to_add then Hashtbl.add h id (r, n, name, limit);
    inst_model.max <- max inst_model.max !n;
    Thread.yield ();
    true
  end


let reset_inst inst_model =
  Hashtbl.iter (fun _ (_, n, _, _) -> n := 0) inst_model.h;
  ignore (refresh_instances inst_model ())


let empty_sat_inst inst_model =
  inst_model.max <- 0;
  reset_inst inst_model;
  SAT.empty_with_inst (add_inst inst_model)


exception Abort_thread

let update_status image label buttonclean env s steps =
  let satmode = (* smtfile() || smt2file() ||  satmode()*) false in
  match s with
  | FE.Unsat (d,dep) ->
    let time = Options.Time.value () in
    if not satmode then Loc.report std_formatter d.st_loc;
    if satmode then printf "@{<C.F_Red>unsat@}@."
    else printf "@{<C.F_Green>Valid@} (%2.4f) (%d)@." time steps;
    if unsat_core () then begin
      printf "unsat-core:\n%a@." (Explanation.print_unsat_core ~tab:true) dep;
      show_used_lemmas env dep
    end;
    image#set_stock `YES;
    label#set_text (sprintf "  Valid (%2.2f s)" time);
    buttonclean#misc#show ();
    ignore(buttonclean#connect#clicked
             ~callback:(fun () -> prune_unused env))

  | FE.Inconsistent d ->
    if not satmode then
      (Loc.report std_formatter d.st_loc;
       fprintf fmt "Inconsistent assumption@.")
    else printf "unsat@.";
    image#set_stock `EXECUTE;
    label#set_text "  Inconsistent assumption"

  | FE.Unknown (d, t) ->
    if not satmode then
      (Loc.report std_formatter d.st_loc; printf "I don't know.@.")
    else printf "unknown@.";
    image#set_stock `NO;
    label#set_text (sprintf "  I don't know (%2.2f s)"
                      (Options.Time.value()));
    if model () then pop_model t ()

  | FE.Sat (d, t) ->
    if not satmode then Loc.report std_formatter d.st_loc;
    if satmode then printf "unknown (sat)@."
    else printf "I don't know@.";
    image#set_stock `NO;
    label#set_text
      (sprintf "  I don't know (sat) (%2.2f s)" (Options.Time.value()));
    if model () then pop_model t ()

  | FE.Timeout _ ->
    assert false (* should not happen in GUI ? *)

  | FE.Preprocess ->
    assert false (* should not happen in GUI ! *)

let update_aborted image label buttonstop buttonrun timers_model = function
  | Abort_thread ->
    Options.Time.unset_timeout ~is_gui:true;
    Timers.update timers_model.timers;
    if debug () then fprintf fmt "alt-ergo thread terminated@.";
    image#set_stock `DIALOG_QUESTION;
    label#set_text "  Process aborted";
    buttonstop#misc#hide ();
    buttonrun#misc#show ()
  | Util.Timeout ->
    Options.Time.unset_timeout ~is_gui:true;
    Timers.update timers_model.timers;
    if debug () then
      fprintf fmt "alt-ergo thread terminated (timeout)@.";
    image#set_stock `CUT;
    label#set_text "  Timeout";
    buttonstop#misc#hide ();
    buttonrun#misc#show ()
  | e ->
    Options.Time.unset_timeout ~is_gui:true;
    Timers.update timers_model.timers;
    let message = sprintf "Error: %s" (Printexc.to_string e) in
    if debug () then fprintf fmt "alt-ergo thread terminated@.";
    image#set_stock `DIALOG_ERROR;
    label#set_text (" "^message);
    buttonstop#misc#hide ();
    buttonrun#misc#show ();
    fprintf fmt "%s@." message;
    pop_error ~error:true ~message ()



let wrapper_update_status image label buttonclean env s steps =
  GtkThread.sync (fun () ->
      update_status image label buttonclean env s steps
    ) ()

let wrapper_update_aborted image label buttonstop buttonrun timers_model e =
  GtkThread.async (fun () ->
      update_aborted image label buttonstop buttonrun timers_model e
    ) ()

let wrapper_reset buttonstop buttonrun =
  GtkThread.async (fun () ->
      buttonstop#misc#hide ();
      buttonrun#misc#show ()
    ) ()

let wrapper_refresh_instances inst_model =
  GtkThread.async (fun () ->
      ignore (refresh_instances inst_model ())
    )

let wrapper_refresh_timers timers_model =
  GtkThread.async (fun () ->
      ignore (refresh_timers timers_model ())
    )

let interrupt = ref None

let vt_signal =
  match Sys.os_type with
  | "Win32" -> Sys.sigterm
  | _ -> Sys.sigvtalrm

let force_interrupt old_action_ref n =
  (* This function is called just before the thread's timeslice ends *)
  if Stdlib.(=) (Some (Thread.id(Thread.self()))) !interrupt then
    raise Abort_thread;
  match !old_action_ref with
  | Sys.Signal_handle f -> f n
  | _ -> fprintf fmt "Not in threaded mode@."



let kill_thread thread () =
  match !thread with
  | Some r ->
    interrupt :=  Some (Thread.id r);
    Thread.join r
  | _ ->
    interrupt := None


let run_replay env used_context =
  let ast = to_ast env.ast in
  if debug () then fprintf fmt "AST : \n-----\n%a@." print_typed_decl_list ast;

  let ast_pruned = [ast] in

  Options.Time.start ();
  Options.Time.set_timeout ~is_gui:true (Options.timelimit ());
  List.iter
    (fun dcl ->
       let cnf = Cnf.make_list dcl in
       ignore (List.fold_left
                 (FE.process_decl FE.print_status used_context)
                 (empty_sat_inst env.insts, true, Explanation.empty) cnf)
    ) ast_pruned;
  Options.Time.unset_timeout ~is_gui:true


let run buttonrun buttonstop buttonclean inst_model timers_model
    image label thread env used_context () =

  Profiling.init ();

  (* Install the signal handler: *)
  let old_action_ref = ref Sys.Signal_ignore in
  let old_action =
    Sys.signal vt_signal (Sys.Signal_handle (force_interrupt old_action_ref)) in
  old_action_ref := old_action;

  image#set_stock `EXECUTE;
  label#set_text "  ...";
  buttonstop#misc#show ();
  buttonrun#misc#hide ();
  buttonclean#misc#hide ();
  clear_used_lemmas_tags env;

  let ast = to_ast env.ast in
  if debug () then fprintf fmt "AST : \n-----\n%a@." print_typed_decl_list ast;

  let ast_pruned = [ast] in

  (* refresh instances *)
  let to_id =
    GMain.Timeout.add ~ms:300 ~callback:(refresh_instances inst_model)
  in
  let ti_id =
    GMain.Timeout.add ~ms:500 ~callback:(refresh_timers timers_model)
  in

  reset_timers timers_model;

  thread :=
    Some
      (Thread.create
         (fun () ->
            (try
               (* Thread.yield (); *)
               if debug () then fprintf fmt "Starting alt-ergo thread@.";
               Options.Time.start ();
               Options.Time.set_timeout ~is_gui:true (Options.timelimit ());
               Timers.set_timer_start (Timers.start timers_model.timers);
               Timers.set_timer_pause (Timers.pause timers_model.timers);

               List.iter
                 (fun dcl ->
                    let cnf = Cnf.make_list dcl in
                    ignore
                      (List.fold_left
                         (FE.process_decl
                            (wrapper_update_status image label buttonclean env)
                            used_context)
                         (empty_sat_inst inst_model, true, Explanation.empty)
                         cnf)
                 ) ast_pruned;

               Options.Time.unset_timeout ~is_gui:true
             with e ->
               wrapper_update_aborted
                 image label buttonstop buttonrun timers_model e
            );
            if debug () then fprintf fmt "Send done signal to waiting thread@.";
            wrapper_reset buttonstop buttonrun;
            Thread.delay 0.001;
            GMain.Timeout.remove to_id;
            GMain.Timeout.remove ti_id;
            wrapper_refresh_instances inst_model ();
            wrapper_refresh_timers timers_model ();
         ) ());

  Thread.yield ()

let remove_context env () =
  List.iter
    (fun (td, _) ->
       match td.c with
       | APredicate_def (_, _, _, _) ->
         toggle_prune env td
       | AAxiom (_, s, _, _)
         when String.length s = 0 ||
              (Stdlib.(<>) s.[0] '_'  &&
               Stdlib.(<>) s.[0] '@') ->
         toggle_prune env td
       | _ -> ()
    ) env.ast


let set_ctrl env b key =
  let open GdkKeysyms in
  let k = GdkEvent.Key.keyval key in
  if k == _Control_L || k == _Control_R then
    (env.ctrl <- b; true)
  else false

let empty_error_model () =
  let rcols = new GTree.column_list in
  let rcol_icon = rcols#add GtkStock.conv in
  let rcol_desc = rcols#add Gobject.Data.string in
  let rcol_line = rcols#add Gobject.Data.int in
  let rcol_type = rcols#add Gobject.Data.int in
  let rcol_color = rcols#add Gobject.Data.string in
  {
    some = false;
    rcols = rcols;
    rcol_icon = rcol_icon;
    rcol_desc = rcol_desc;
    rcol_line = rcol_line;
    rcol_type = rcol_type;
    rcol_color = rcol_color;
    rstore = GTree.list_store rcols;
  }


let goto_error (view:GTree.view) error_model buffer
    (sv:GSourceView2.source_view)  path _column =
  let model = view#model in
  let row = model#get_iter path in
  let line = model#get ~row ~column:error_model.rcol_line in
  let iter_line = buffer#get_iter (`LINE (line-1)) in
  let iter_endline = iter_line#forward_line#backward_char in
  buffer#select_range iter_endline iter_line;
  ignore(sv#scroll_to_iter  ~use_align:true ~yalign:0.1 iter_line)


let create_error_view error_model buffer sv ~packing () =
  let view = GTree.view ~model:error_model.rstore ~packing () in

  let renderer = GTree.cell_renderer_pixbuf [] in
  let col = GTree.view_column ~title:""
      ~renderer:(renderer, ["stock_id", error_model.rcol_icon]) () in
  ignore (view#append_column col);
  col#set_sort_column_id error_model.rcol_icon.GTree.index;

  let renderer = GTree.cell_renderer_text [] in
  let col = GTree.view_column ~title:"Line"
      ~renderer:(renderer, ["text", error_model.rcol_line]) () in
  ignore (view#append_column col);
  col#set_resizable true;
  col#set_sort_column_id error_model.rcol_line.GTree.index;

  let renderer = GTree.cell_renderer_text [] in
  let col = GTree.view_column ~title:"Description"
      ~renderer:(renderer, ["text", error_model.rcol_desc]) () in
  ignore (view#append_column col);
  col#set_resizable true;
  col#set_sort_column_id error_model.rcol_desc.GTree.index;

  ignore(view#connect#row_activated
           ~callback:(goto_error view error_model buffer sv));
  view



let goto_lemma (view:GTree.view) inst_model buffer
    (sv:GSourceView2.source_view) env path _column =
  let model = view#model in
  let row = model#get_iter path in
  let id = model#get ~row ~column:inst_model.icol_tag in
  try
    let line, t = find_line id env.ast in
    let iter_line = buffer#get_iter (`LINE (line-1)) in
    let prev_line = buffer#get_iter (`LINE (line-2)) in
    buffer#place_cursor ~where:iter_line;
    ignore(sv#scroll_to_iter ~use_align:true ~yalign:0.1 prev_line);
    env.last_tag#set_properties
      [`BACKGROUND_SET false; `UNDERLINE_SET false];
    t#set_property (`BACKGROUND "light blue");
    env.last_tag <- t;
  with Not_found -> ()


let colormap = Gdk.Color.get_system_colormap ()

let set_color_inst inst_model renderer (istore:GTree.model) row =
  let id = istore#get ~row ~column:inst_model.icol_tag in
  let _, nb_inst, _, limit = Hashtbl.find inst_model.h id in
  (* let nb_inst = istore#get ~row ~column:inst_model.icol_number in *)
  (* let limit = istore#get ~row ~column:inst_model.icol_limit in *)
  let nb_inst = !nb_inst in
  let limit = !limit in
  if nb_inst = limit then
    renderer#set_properties [`FOREGROUND "blue"]
  else if inst_model.max <> 0 then
    let perc = (nb_inst * 65535) / inst_model.max in
    let red_n =
      Gdk.Color.alloc ~colormap (`RGB (perc, 0, 0)) in
    renderer#set_properties [`FOREGROUND_GDK red_n]
  else
    renderer#set_properties [`FOREGROUND_SET false];
  Thread.yield ()


let create_inst_view inst_model env buffer sv ~packing () =
  let view = GTree.view ~model:inst_model.istore ~packing () in

  view#selection#set_mode `MULTIPLE;
  let renderer = GTree.cell_renderer_pixbuf [] in
  let col = GTree.view_column ~title:""
      ~renderer:(renderer, ["stock_id", inst_model.icol_icon]) () in
  ignore (view#append_column col);
  col#set_sort_column_id inst_model.icol_icon.GTree.index;

  let renderer = GTree.cell_renderer_text [] in
  let col = GTree.view_column ~title:"#"
      ~renderer:(renderer, ["text", inst_model.icol_number]) () in
  ignore (view#append_column col);
  col#set_cell_data_func renderer
    (set_color_inst inst_model renderer);
  col#set_resizable true;
  col#set_sort_column_id inst_model.icol_number.GTree.index;

  let renderer = GTree.cell_renderer_text [`EDITABLE true] in
  ignore (renderer#connect#edited ~callback:(fun _path s ->
      let limit = try int_of_string s with Failure _ -> -1 in
      List.iter (fun path ->
          let row = inst_model.istore#get_iter path in
          let id = inst_model.istore#get ~row ~column:inst_model.icol_tag in
          let _, _, name,l = Hashtbl.find inst_model.h id in
          if limit >= 0 then
            begin
              l := limit;
              inst_model.istore#set ~row ~column:inst_model.icol_limit
                (string_of_int limit);
              Gui_session.save env.actions
                (Gui_session.LimitLemma (id, name,limit))
            end
          else
            begin
              l := -1;
              inst_model.istore#set ~row ~column:inst_model.icol_limit inf;
              Gui_session.save env.actions (Gui_session.UnlimitLemma (id, name))
            end
        ) view#selection#get_selected_rows
    ));
  let col = GTree.view_column ~title:"limit"
      ~renderer:(renderer, ["text", inst_model.icol_limit]) () in
  ignore (view#append_column col);
  col#set_resizable true;
  col#set_sort_column_id inst_model.icol_limit.GTree.index;

  let renderer = GTree.cell_renderer_text [] in
  let col = GTree.view_column ~title:"Lemma"
      ~renderer:(renderer, ["text", inst_model.icol_desc]) () in
  ignore (view#append_column col);
  col#set_cell_data_func renderer
    (set_color_inst inst_model renderer);
  col#set_resizable true;
  col#set_sort_column_id inst_model.icol_desc.GTree.index;


  ignore(view#connect#row_activated
           ~callback:(goto_lemma view inst_model buffer sv env));
  view


let next_begins i buf found_all_tag =
  let iter = ref i in
  while !iter#compare buf#end_iter < 0 &&
        not (!iter#begins_tag (Some found_all_tag)) do
    iter := !iter#forward_to_tag_toggle (Some found_all_tag)
  done;
  if !iter#compare buf#end_iter >= 0 then raise Not_found;
  !iter

let prev_ends i buf found_all_tag =
  let iter = ref i in
  while !iter#compare buf#start_iter > 0 &&
        not (!iter#ends_tag (Some found_all_tag)) do
    iter := !iter#backward_to_tag_toggle (Some found_all_tag)
  done;
  if !iter#compare buf#start_iter <= 0 then raise Not_found;
  !iter

let search_next ?(backward=false) (sv:GSourceView2.source_view)
    (buf:sbuffer) found_tag found_all_tag () =
  try
    let iter = buf#get_iter_at_char buf#cursor_position in
    buf#remove_tag found_tag ~start:buf#start_iter ~stop:buf#end_iter;
    let i1 =
      if backward then prev_ends iter buf found_all_tag
      else next_begins iter buf found_all_tag
    in
    let i2 =
      if backward then i1#backward_to_tag_toggle (Some found_all_tag)
      else i1#forward_to_tag_toggle (Some found_all_tag)
    in
    buf#apply_tag found_tag ~start:i1 ~stop:i2;
    ignore(sv#scroll_to_iter
             ~use_align:true ~yalign:0.1 i1#backward_line);
    buf#place_cursor ~where:i2
  with Not_found -> ()

let search_one buf str result iter found_all_tag =
  result :=
    GSourceView2.iter_forward_search !iter []
      ~start:buf#start_iter ~stop:buf#end_iter str;
  match !result with
  | None -> ()
  | Some (i1, i2) ->
    buf#apply_tag found_all_tag ~start:i1 ~stop:i2;
    iter := i2

let search_all entry (_sv:GSourceView2.source_view)
    (buf:sbuffer) found_tag found_all_tag () =
  buf#remove_tag found_tag ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag found_all_tag ~start:buf#start_iter ~stop:buf#end_iter;
  let str = entry#text in
  let iter = ref buf#start_iter in
  if Stdlib.(<>) str "" then
    let result = ref None in
    search_one buf str result iter found_all_tag;
    while !result != None do
      search_one buf str result iter found_all_tag
    done


let start_gui all_used_context =
  Options.set_timers true;
  Options.set_thread_yield Thread.yield;

  (* TODO: crash : change this*)
  set_timeout (fun () -> printf "Timeout@."; raise Util.Timeout);


  let w =
    GWindow.window
      ~title:"AltGr-Ergo"
      ~allow_grow:true
      ~allow_shrink:true
      ~position:`CENTER
      ~width:window_width
      ~height:window_height ()
  in

  ignore (w#misc#connect#size_allocate ~callback:(fun r ->
      Gui_config.update_window_size r.Gtk.width r.Gtk.height));

  let lmanager = GSourceView2.source_language_manager ~default:true in
  lmanager#set_search_path
    (String.concat Filename.dir_sep
       [Config.datadir; "gtksourceview-2.0"; "language-specs"] ::
     lmanager#search_path);
  let source_language = lmanager#language "alt-ergo" in

  let smanager = GSourceView2.source_style_scheme_manager ~default:true in
  let scheme = smanager#style_scheme Gui_config.style in
  let filename = get_file () in
  let preludes = Options.preludes () in
  let pfile = Parsers.parse_problem ~filename ~preludes in
  (* TODO: is the GUI ever invoked in parse_only mode ? *)
  if parse_only () then exit 0;
  let typed_ast, _ = Typechecker.type_file pfile in
  (* TODO: is the GUI ever invoked in type_only mode ? *)
  if type_only () then exit 0;
  let typed_ast = Typechecker.split_goals typed_ast in

  let main_vbox = GPack.vbox
      ~homogeneous:false ~border_width:0 ~packing:w#add () in

  let menubar = GMenu.menu_bar ~packing:main_vbox#pack () in

  let notebook =
    GPack.notebook ~border_width:0 ~tab_pos:`BOTTOM
      ~show_border:false
      ~enable_popup:true
      ~scrollable:true
      ~packing:main_vbox#add () in

  let note_search = Hashtbl.create 7 in


  let session_cin =
    try Some (open_in_bin (get_session_file()))
    with Sys_error _ -> None in

  let envs =
    List.fold_left
      (fun acc (l, goal_name) ->
         let used_context =
           FE.choose_used_context all_used_context ~goal_name
         in
         let buf1 = match source_language with
           | Some language ->
             GSourceView2.source_buffer ~language
               ~highlight_syntax:true ~highlight_matching_brackets:true ()
           | None -> GSourceView2.source_buffer () in

         let buf2 = match source_language with
           | Some language ->
             GSourceView2.source_buffer ~language
               ~highlight_syntax:true ~highlight_matching_brackets:true ()
           | None -> GSourceView2.source_buffer () in

         buf1#set_style_scheme scheme;
         buf2#set_style_scheme scheme;

         let annoted_ast = annot buf1 l in
         if debug () then fprintf fmt "Computing dependencies ... ";
         let dep = make_dep annoted_ast in
         if debug () then fprintf fmt "Done@.";


         let text = List.fold_left
             (fun _ (td,_) ->
                match td.c with
                | AGoal (_, Thm, s, _) -> "goal "^s
                | AGoal (_, Check, s, _) -> "check "^s
                | AGoal (_, Cut, s, _) -> "cut "^s
                | _ -> "Empty"
             ) "" annoted_ast in

         let label = GMisc.label ~text () in
         let nb_page = ref 0 in
         let append g =
           nb_page := notebook#append_page ~tab_label:label#coerce g in

         let eventBox = GBin.event_box ~border_width:0 ~packing:append () in


         let vbox = GPack.vbox
             ~homogeneous:false ~border_width:0 ~packing:eventBox#add () in

         let rbox = GPack.vbox ~border_width:0 ~packing:vbox#add () in


         let toolbox = GPack.hbox ~border_width:0 ~packing:rbox#pack () in

         let toolbar = GButton.toolbar ~tooltips:true ~packing:toolbox#add () in
         toolbar#set_icon_size `DIALOG;

         let hb = GPack.paned `HORIZONTAL
             ~border_width:3 ~packing:rbox#add () in

         let vb1 = GPack.paned `VERTICAL
             ~border_width:3 ~packing:(hb#pack1 ~shrink:true ~resize:true) () in
         let vb2 = GPack.paned `VERTICAL
             ~border_width:3 ~packing:(hb#pack2 ~shrink:true ~resize:true) () in

         let fr1 = GBin.frame ~shadow_type:`ETCHED_OUT
             ~width:(60 * window_width / 100)
             ~height:(50 * window_height / 100)
             ~packing:(vb1#pack1 ~shrink:true ~resize:true) () in

         let fr2 = GBin.frame ~shadow_type:`ETCHED_OUT
             ~height:(15 * window_height / 100)
             ~packing:(vb2#pack1 ~shrink:true ~resize:true) () in

         let fr3 = GBin.frame ~shadow_type:`ETCHED_OUT ~show:false
             ~height:(5 * window_height / 100)
             ~packing:(vb1#pack2 ~shrink:true ~resize:true) () in

         let binfo = GPack.vbox ~border_width:0
             ~packing:(vb2#pack2 ~shrink:true ~resize:true) () in

         let fr4 = GBin.frame ~shadow_type:`ETCHED_OUT
             ~packing:binfo#add () in

         let fr5 = GBin.frame ~shadow_type:`NONE
             ~packing:binfo#pack () in

         let table_timers = GPack.table ~columns:3 ~rows:8
             ~row_spacings:1 ~col_spacings:8 ~border_width:4
             ~packing:fr5#add () in


         let st = GMisc.statusbar ~has_resize_grip:false ~border_width:0
             ~packing:vbox#pack () in
         let st_ctx = st#new_context ~name:"Type" in

         let error_model = empty_error_model () in
         let inst_model = empty_inst_model () in
         let timers_model = empty_timers_model table_timers in


         let resulting_ids = compute_resulting_ids annoted_ast in
         let actions = Gui_session.read_actions resulting_ids session_cin in

         let sw1 = GBin.scrolled_window
             ~vpolicy:`AUTOMATIC
             ~hpolicy:`AUTOMATIC
             ~packing:fr1#add ()
         in
         let tv1 =
           GSourceView2.source_view ~source_buffer:buf1 ~packing:(sw1#add)
             ~show_line_numbers:true ~wrap_mode:(if wrap then `CHAR else `NONE)
             ~highlight_current_line:true ()
         in
         let _ = tv1#misc#modify_font monospace_font in
         let _ = tv1#set_editable false in

         let sw2 = GBin.scrolled_window
             ~vpolicy:`AUTOMATIC
             ~hpolicy:`AUTOMATIC
             ~packing:fr2#add ()
         in
         let tv2 =
           GSourceView2.source_view ~source_buffer:buf2 ~packing:(sw2#add)
             ~show_line_numbers:false ~wrap_mode:(if wrap then `CHAR else `NONE)
             ~highlight_current_line:true ()
         in
         let _ = tv2#misc#modify_font monospace_font in
         let _ = tv2#set_editable false in


         let env = create_env buf1 tv1 buf2 tv2 error_model inst_model
             st_ctx annoted_ast dep actions resulting_ids in
         connect env;

         ignore (toolbar#insert_toggle_button
                   ~text:" Remove context"
                   ~icon:(GMisc.image ~stock:`CUT
                            ~icon_size:`LARGE_TOOLBAR ())#coerce
                   ~callback:(remove_context env) ());

         let buttonrun = toolbar#insert_button
             ~text:" Run Alt-Ergo"
             ~icon:(GMisc.image ~stock:`EXECUTE  ~icon_size:`LARGE_TOOLBAR()
                   )#coerce () in

         let buttonstop = toolbar#insert_button
             ~text:" Abort"
             ~icon:(GMisc.image ~stock:`STOP  ~icon_size:`LARGE_TOOLBAR()
                   )#coerce () in
         buttonstop#misc#hide ();

         toolbar#insert_space ();

         let resultbox = GPack.hbox () in
         let result_image = GMisc.image ~icon_size:`LARGE_TOOLBAR
             ~stock:`DIALOG_QUESTION ~packing:resultbox#add () in
         let result_label = GMisc.label
             ~text:" " ~packing:resultbox#add () in

         ignore(toolbar#insert_widget resultbox#coerce);

         let buttonclean = toolbar#insert_button
             ~text:" Clean unused"
             ~icon:(GMisc.image ~stock:`CLEAR  ~icon_size:`LARGE_TOOLBAR()
                   )#coerce () in
         buttonclean#misc#hide ();

         let toolsearch =
           GButton.toolbar ~tooltips:true ~packing:(toolbox#pack ~fill:true) ()
         in
         toolsearch#set_icon_size `DIALOG;

         let search_box = GPack.hbox ~spacing:5 ~border_width:5 () in
         ignore(GMisc.image ~icon_size:`LARGE_TOOLBAR
                  ~stock:`FIND ~packing:search_box#add ());
         let search_entry = GEdit.entry ~packing:search_box#add () in

         ignore(toolsearch#insert_widget search_box#coerce);

         let button_seach_forw = toolsearch#insert_button
             (* ~text:"Search" *)
             ~icon:(GMisc.image ~stock:`GO_DOWN  ~icon_size:`LARGE_TOOLBAR()
                   )#coerce () in
         let button_seach_back = toolsearch#insert_button
             (* ~text:"Search" *)
             ~icon:(GMisc.image ~stock:`GO_UP  ~icon_size:`LARGE_TOOLBAR()
                   )#coerce () in

         let found_all_tag = buf1#create_tag [`BACKGROUND "yellow"] in
         let found_tag = buf1#create_tag [`BACKGROUND "orange"] in

         ignore(search_entry#connect#changed
                  ~callback:(search_all search_entry
                               tv1 buf1 found_tag found_all_tag));

         ignore(search_entry#event#connect#key_press
                  ~callback:(fun k ->
                      if GdkEvent.Key.keyval k = GdkKeysyms._Return then begin
                        search_next tv1 buf1 found_tag found_all_tag ();
                        true
                      end
                      else false
                    ));

         ignore(button_seach_forw#connect#clicked
                  ~callback:(search_next tv1 buf1 found_tag found_all_tag));
         ignore(button_seach_back#connect#clicked
                  ~callback:(search_next ~backward:true
                               tv1 buf1 found_tag found_all_tag));



         let sw3 = GBin.scrolled_window
             ~vpolicy:`AUTOMATIC
             ~hpolicy:`AUTOMATIC
             ~packing:fr3#add ()
         in
         ignore(create_error_view error_model env.buffer tv1
                  ~packing:sw3#add ());

         add_to_buffer error_model env.buffer env.ast;
         env.buffer#place_cursor ~where:buf1#start_iter;

         if error_model.some then fr3#misc#show ();

         let sw4 = GBin.scrolled_window
             ~vpolicy:`AUTOMATIC
             ~hpolicy:`AUTOMATIC
             ~packing:fr4#add ()
         in

         ignore(create_inst_view inst_model env env.buffer tv1
                  ~packing:sw4#add ());


         Gui_replay.replay_session env;
         ignore (refresh_instances env.insts ());

         let thread = ref None in

         ignore(buttonrun#connect#clicked
                  ~callback:(
                    run buttonrun buttonstop buttonclean inst_model timers_model
                      result_image result_label thread env used_context));

         ignore(buttonstop#connect#clicked
                  ~callback:(kill_thread thread));

         ignore(eventBox#event#connect#key_press
                  ~callback:(set_ctrl env true));

         ignore(eventBox#event#connect#key_release
                  ~callback:(set_ctrl env false));

         Hashtbl.add note_search !nb_page
           (search_entry,
            run buttonrun buttonstop buttonclean inst_model
              timers_model result_image result_label thread env used_context);

         env::acc

      ) [] typed_ast in

  begin
    match session_cin with
    | Some c -> close_in c
    | None -> ()
  end;

  let envs = List.rev envs in

  let file_entries = [
    `I ("Save session", save_dialog "Cancel" envs);
    `S;
    `I ("Quit", quit envs)
  ] in

  let not_implemented _ = eprintf "Not implemented@."
  in


  let set_wrap_lines _ =
    List.iter (fun env ->
        if Stdlib.(=) env.goal_view#wrap_mode `NONE then (
          env.goal_view#set_wrap_mode `CHAR;
          env.inst_view#set_wrap_mode `CHAR;
          Gui_config.update_wrap true
        ) else (
          env.goal_view#set_wrap_mode `NONE;
          env.inst_view#set_wrap_mode `NONE;
          Gui_config.update_wrap false
        )) envs
  in


  let choose_font () =
    let font_win = GWindow.font_selection_dialog
        ~parent:w
        ~destroy_with_parent:true
        ~modal:true
        ~position:`CENTER_ON_PARENT () in
    ignore (
      font_win#ok_button#connect#clicked ~callback:(fun () ->
          set_font envs font_win#selection#font_name)
    );
    ignore (font_win#run ());
    ignore (font_win#misc#hide ())
  in


  let debug_entries = [
    `C ("SAT", debug_sat (), set_debug_sat);
    `S;
    `C ("CC", debug_cc (), set_debug_cc);
    `C ("Use", debug_use (), set_debug_use);
    `C ("UF", debug_uf (), set_debug_uf);
    `C ("AC", debug_ac (), set_debug_ac);
    `S;
    `C ("Arith", debug_arith (), set_debug_arith);
    `C ("Fourier-Motzkin", debug_fm (), set_debug_fm);
    `C ("Arrays", debug_arrays (), set_debug_arrays);
    `C ("Bit-vectors", debug_bitv (), set_debug_bitv);
    `C ("Sum", debug_sum (), set_debug_sum);
    `C ("Records", false, not_implemented);
    `S;
    `C ("Case split", debug_split (), set_debug_split);
    `C ("Replay unsat cores", debug_unsat_core (), set_debug_unsat_core);
    `C ("Typing", debug_typing (), set_debug_typing);
    `C ("Verbose", verbose (), set_verbose);
  ] in

  let options_entries =
    let set_complete_model b =
      if b then set_model MComplete else set_model MNone in
    let set_all_models b =
      if b then set_model MAll else set_model MNone in
    let set_model b = if b then set_model MDefault else set_model MNone in
    [
      `C ("Unsat cores", unsat_core (), set_unsat_core);
      `S;
      `C ("Model", model (), set_model);
      `C ("Complete model", complete_model (), set_complete_model);
      `C ("All models", all_models (), set_all_models);
      `S;
      `C ("Variables in triggers", triggers_var (), set_triggers_var);
      `C ("Greedy", greedy (), set_greedy);
      `C ("Contra congruence", not (no_contracongru ()),
          fun b -> set_no_contracongru (not b));
      `S;
      `C ("Restricted", restricted (), set_restricted);
      `S;
      `C ("Wrap lines", wrap, set_wrap_lines);
      `S;
      `I ("Change font", choose_font);
      `I ("Increase font size", fun () -> increase_size envs);
      `I ("Decrease font size", fun () -> decrease_size envs);
      `I ("Reset font size", fun () -> reset_size envs);
    ] in

  let help_entries = [
    `I ("About", show_about);
  ] in

  (* let entries = [ *)
  (*   `M ("File", file_entries); *)
  (*   `M ("Debug", debug_entries); *)
  (*   `M ("Options", options_entries); *)
  (*   `M ("Help", help_entries) *)
  (* ] in *)

  let create_menu label menubar =
    let item = GMenu.menu_item ~label ~packing:menubar#append () in
    GMenu.menu ~packing:item#set_submenu ()
  in

  let menu = create_menu "File" menubar in
  GToolbox.build_menu menu ~entries:file_entries;

  let menu = create_menu "Debug" menubar in
  GToolbox.build_menu menu ~entries:debug_entries;

  let menu = create_menu "Options" menubar in
  GToolbox.build_menu menu ~entries:options_entries;

  let menu = create_menu "Help" menubar in
  GToolbox.build_menu menu ~entries:help_entries;


  let focus_search () =
    let p = notebook#current_page in
    let e, _ = Hashtbl.find note_search p in
    e#misc#grab_focus ()
  in

  let launch_run () =
    let p = notebook#current_page in
    let _, r = Hashtbl.find note_search p in
    r ()
  in

  let mod_mask = [`MOD2 ; `MOD3 ; `MOD4 ; `MOD5 ; `LOCK] in

  let key_press ev =
    let key_ev = GdkEvent.Key.keyval ev in
    let mods_ev = List.filter
        (fun m -> not (List.mem m mod_mask)) (GdkEvent.Key.state ev) in
    match mods_ev with
    | [`CONTROL] ->
      (match key_ev with
       | k when k = GdkKeysyms._q -> quit envs (); true
       | k when k = GdkKeysyms._s -> save_dialog "Cancel" envs (); true
       | k when k = GdkKeysyms._f -> focus_search (); true
       | k when k = GdkKeysyms._r -> launch_run (); true
       | k when k = GdkKeysyms._equal || k = GdkKeysyms._plus ->
         increase_size envs; true
       | k when k = GdkKeysyms._minus ->
         decrease_size envs; true
       | k when k = GdkKeysyms._0 || k = GdkKeysyms._KP_0 ->
         reset_size envs; true
       | _ -> false)
    | _ -> false
  in

  ignore (w#event#connect#key_press ~callback:(key_press));

  ignore(w#connect#destroy ~callback:(quit envs));
  w#show ();

  (* Thread.join(GtkThread.start ()); *)
  GtkThread.main ()

let start_replay session_cin all_used_context =
  let filename = get_file () in
  let preludes = Options.preludes () in
  let pfile = Parsers.parse_problem ~filename ~preludes in
  (* TODO: is the GUI ever invoked in parse_only mode ? *)
  if parse_only () then exit 0;
  let typed_ast, _ = Typechecker.type_file pfile in
  (* TODO: is the GUI ever invoked in type_only mode ? *)
  if type_only () then exit 0;
  let typed_ast = Typechecker.split_goals typed_ast in
  List.iter
    (fun (l, goal_name) ->
       let used_context = FE.choose_used_context all_used_context ~goal_name in

       let buf1 = GSourceView2.source_buffer () in

       let annoted_ast = annot buf1 l in

       let error_model = empty_error_model () in
       let inst_model = empty_inst_model () in

       let resulting_ids = compute_resulting_ids annoted_ast in
       let actions = Gui_session.read_actions resulting_ids session_cin in


       (* cradingue *)
       let env = create_replay_env buf1 error_model inst_model annoted_ast
           actions resulting_ids in

       add_to_buffer error_model env.buffer env.ast;

       Gui_replay.replay_session env;
       run_replay env used_context

    ) typed_ast;

  begin
    match session_cin with
    | Some c -> close_in c
    | None -> ()
  end


let () =
  if not (model ()) then
    try
      Sys.set_signal Sys.sigalrm
        (Sys.Signal_handle (fun _ -> Options.exec_timeout ()))
    with Invalid_argument _ -> ()

let () =
  let all_used_context = FE.init_all_used_context () in
  try
    Options.set_is_gui true;
    if replay() then
      start_replay (Some (open_in_bin (get_session_file()))) all_used_context
    else start_gui all_used_context
  with
  | Sys_error _ -> start_gui all_used_context
  | Util.Timeout ->
    Format.eprintf "Timeout@.";
    exit 142
