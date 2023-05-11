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

#!/usr/bin/env -S ocaml unix.cma

(* Configure script

   goal: register some static configuration & check dependencies
   Steps executed:
   - parse command line options
   - compute actual config options
   - output these config options in Makefile.config
*)

(* configuration options *)
let prefix = ref ""

let libdir = ref ""

let mandir = ref ""

let static = ref false

let pkg = ref ""

(* this option add the possibility to choose the library that handle numbers in Alt-Ergo between zarith and nums *)
type numbers_lib =
  | Nums
  | Zarith

let print_numbers_lib = function
  | Nums -> "Nums"
  | Zarith -> "Zarith"

let numbers_lib = ref Zarith

let set_numbers_lib s =
  match s with
  | "nums" | "Nums" -> numbers_lib := Nums
  | "zarith" | "Zarith" -> numbers_lib := Zarith
  | _ ->
    Format.eprintf "Unknown library name %s, use Nums or Zarith@." s;
    exit 1

(* Parse command line arguments *)
let () =
  let args =
    Arg.align
      [
        ("--prefix", Arg.Set_string prefix, "<path> prefix directory");
        ("--libdir", Arg.Set_string libdir, "<path> lib directory");
        ("--mandir", Arg.Set_string mandir, "<path> man directory");
        ("--static", Arg.Set static, " Enable statically compilation");
        ("--numbers-lib", Arg.String set_numbers_lib, " Choose numbers library between Zarith and Nums");
      ]
  in
  let anon_fun s =
    match !pkg with
    | "" -> pkg := s
    | _ ->
      Format.eprintf "Anonymous argument ignored: '%s'@." s;
      exit 1
  in
  let usage = "./configure [options]" in
  Arg.parse args anon_fun usage

(* Small wrapper to read all the contents of a channel *)
let read_all ch =
  let b = Buffer.create 113 in
  try
    while true do
      Buffer.add_channel b ch 30
    done;
    assert false
  with End_of_file -> Buffer.contents b

(* lazily check that opam is present *)
let opam_check = lazy (
  let cmd = Format.asprintf "which opam" in
  let ch = Unix.open_process_in cmd in
  let _ = read_all ch in
  let res = Unix.close_process_in ch in
  match res with
  | Unix.WEXITED 0 ->
    Format.printf "Found opam in path.@."
  | _ ->
    Format.eprintf "ERROR: Couldn't find opam in env.@\n%a@."
      Format.pp_print_text "To solve this, you can either install opam, \
                            provide an explicit value to the `--prefix` argument \
                            of this script.";
    exit 1
)

(* Small wrapper to set options *)
let update name r f =
  match !r with
  | "" ->
    r := f ();
    Format.printf "Using default value for '%s' : %s@." name !r
  | s ->
    Format.printf "Using provided value for '%s' : %s@." name s

(* small wrapper around opam var *)
let opam_var v =
  let () = Lazy.force opam_check in
  let cmd = Format.asprintf "opam config var --readonly %s" v in
  let env = Array.append [| "OPAMCLI=2.0" |] (Unix.environment ()) in
  let (ch, _, _) as proc = Unix.open_process_full cmd env in
  let s = input_line ch in
  let _ = Unix.close_process_full proc in
  s


(* Compute actual values for config options *)
let () =
  if !prefix <> "" then begin
    update "prefix" prefix (fun () -> assert false); (* used to print info *)
    update "libdir" libdir (fun () -> Filename.concat !prefix "lib");
    update "mandir" mandir (fun () -> Filename.concat !prefix "man");
    ()
  end else begin
    update "prefix" prefix (fun () -> opam_var "prefix");
    update "libdir" libdir (fun () -> opam_var "lib");
    update "mandir" mandir (fun () -> opam_var "man");
    ()
  end;
  assert (!libdir <> "");
  assert (!mandir <> "");
  ()

(* Output config options into lib/util/config.ml *)
let () =
  let f = Filename.(concat "src" @@ concat "lib" @@ concat "util" "config.ml") in
  let () = Format.printf "Generating file %s..." f in
  let ch = open_out f in
  let fmt = Format.formatter_of_out_channel ch in
  let () =
    Format.fprintf fmt
      "(* Static configuration, automatically generated by configure.ml *)@."
  in
  let () = Format.fprintf fmt {|let libdir = "%s"@.|} !libdir in
  let () = Format.fprintf fmt {|let mandir = "%s"@.|} !mandir in

  let () = Format.fprintf fmt {|type numbers_lib = | Nums | Zarith@.|} in
  let () = Format.fprintf fmt {|let numbers_lib = %s@.|}
      (print_numbers_lib !numbers_lib) in

  let () = Format.fprintf fmt {|
(* Dynamic configuration, relative to the executable path *)

let follow dir path =
  Filename.concat path dir

let abs_exe_path =
  let exe_name = Sys.executable_name in
  if not (Filename.is_relative exe_name) then exe_name
  else begin
    let cwd = Sys.getcwd () in
    Filename.concat cwd exe_name
  end

let datadir =
  abs_exe_path
  |> Filename.dirname
  |> follow Filename.parent_dir_name
  |> follow "lib"
  |> follow "alt-ergo"

let pluginsdir = datadir |> follow "plugins"

let preludesdir = datadir |> follow "preludes"

|} in
  let () = close_out ch in
  let () = Format.printf "done.@." in
  ()

(* Output executable flags into tools/text/flags.dune *)
let () =
  let f = Filename.(concat "src" @@ concat "bin" @@ concat "text" "flags.dune") in
  let () = Format.printf "Generating file %s..." f in
  let ch = open_out f in
  let fmt = Format.formatter_of_out_channel ch in
  let () = Format.fprintf fmt {|(-linkall %s)@.|}
      (if !static then "-cclib -static" else "")
  in
  let () = close_out ch in
  let () = Format.printf "done.@." in
  ()

(* Output config options into Makefile.config *)
let () =
  let () = Format.printf "Generating file Makefile.config..." in
  let ch = open_out "Makefile.config" in
  let fmt = Format.formatter_of_out_channel ch in
  let () = Format.fprintf fmt "# Generated by configure@." in
  let () = Format.fprintf fmt "prefix=%s@." !prefix in
  let () = Format.fprintf fmt "libdir=%s@." !libdir in
  let () = Format.fprintf fmt "mandir=%s@." !mandir in
  let () = close_out ch in
  let () = Format.printf "done.@." in
  ()

let () = Format.printf "Good to go!@."

