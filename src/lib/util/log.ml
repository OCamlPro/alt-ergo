(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2021 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

type 'a log =
  lkey:string ->
  ('a, Format.formatter, unit) format ->
  'a

module H : Hashtbl.S with type key = string =
  Hashtbl.Make (
  struct
    include String
    let hash = Hashtbl.hash
  end
  )

let registered = H.create 23
let display_all = ref false

let register_log (name : string) : unit =
  if H.mem registered name
  then failwith (Format.sprintf "Log key %s registered twice" name)
  else H.add registered name false

let activate_log (name : string) : unit =
  match H.find_opt registered name with
  | None ->
    failwith (Format.sprintf "Cannot activate log %s: it has not been registered" name)
  | Some _ ->
    H.add registered name true

let activate_all () = display_all := true

let is_activated (name : string) : bool =
  !display_all ||
  match H.find_opt registered name with
  | None -> false
  | Some s -> s

let silent (msg : ('a, Format.formatter, unit) format) =
  Format.ifprintf Format.std_formatter msg

let talk
    ?lkey
    ?(fmt = Format.std_formatter)
    (msg : ('a, Format.formatter, unit) format) =
  let () =
    match lkey with
    | None -> ()
    | Some lkey ->
      Format.fprintf fmt "[%s] " lkey in
  Format.fprintf fmt msg

let log
    ~(lkey : string)
    (fmt : Format.formatter)
    (msg : ('a, Format.formatter, unit) format) =
  try
    if is_activated lkey
    then talk ~lkey ~fmt msg
    else silent msg
  with
    Not_found ->
    failwith (Format.sprintf "Log key %s not found" lkey)

let feedback ~(lkey : string) = log ~lkey (Options.get_fmt_std ())
let debug    ~(lkey : string) = log ~lkey (Options.get_fmt_dbg ())
let error    ~(lkey : string) = log ~lkey (Options.get_fmt_err ())
let warn     ~(lkey : string) = log ~lkey (Options.get_fmt_wrn ())
let model    ~(lkey : string) = log ~lkey (Options.get_fmt_mdl ())
let unsat_cr ~(lkey : string) = log ~lkey (Options.get_fmt_usc ())
