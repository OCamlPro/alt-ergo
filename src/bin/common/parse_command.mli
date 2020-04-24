(** {1 Parse_command module used at start-up to parse the command line} *)

(** Only exported function. Calling it will parse the command line options
    and set them accordingly for the rest of the execution *)
val parse_cmdline_arguments : unit -> unit


(** Exception used to exit with corresponding retcode *)
exception Exit_parse_command of int
