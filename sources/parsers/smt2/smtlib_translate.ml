open Options
open Parsed_interface

let translate commands = assert false


let file_parser commands =
  Smtlib_typing.typing commands;
  translate commands

let lexpr_parser l = assert false
let trigger_parser t = assert false
