# Usage

## Library

Since version 2.2.0, Alt-Ergo's library is also compiled and installed. See the [API documentation] for more information.

## Run

Alt-Ergo and AltGr-Ergo are executed with the following commands,
  respectively:

        $ alt-ergo   [options] file.<ext>
        $ altgr-ergo [options] file.<ext>

The CDCL solver is now the default SAT engine. The commands below
allow to enable the old Tableaux-like SAT-solver:

        $ alt-ergo   [options] --sat-solver Tableaux file.<ext>
        $ altgr-ergo [options] --sat-solver Tableaux file.<ext>

### Files extensions
Alt-Ergo supports file extensions:
- `.ae`, for its native input language (`.why` and `.mlw` are now depreciated although still accepted)
- `.psmt2`, `.smt2` for (our polymorphic extension of) the SMT-LIB 2
  standard

See the [Input section] for more information about the format of the input files

### Output
The results of an Alt-ergo's execution have the following form :
```
File "<path_to_file>/<filename>", line <l>, characters <n-m>: <status> (<time in seconde>) (<number of steps> steps) (goal <name of the goal>)
```
The status can be `Valid`, `Invalid` or `I don't know`. If the input file is in the SMT-LIB 2 format the status will be either `unsat`, `sat`, `unknown`. You can force the status to be print in the SMT-LIB 2 form with the option `--output smtlib2`.

### Plugins

See the [AB-Why3 README] file for the documentation of the AB-Why3 plugin

The Fm-Simplex plugin can be used as follows:

        $ alt-ergo --inequalities-plugin fm-simplex-plugin.cmxs [other-options] file.<ext>
        $ alt-ergo --inequalities-plugin some-path/fm-simplex-plugin.cmxs [other-options] file.<ext>

   Alt-Ergo will try to load a local plugin called
   "fm-simplex-plugin.cmxs". If this fails, Alt-Ergo tries to load it
   from the default plugins directory (run `alt-ergo --where plugins`
   to see its absolute path). You can also provide a relative or an
   absolute path as shown by the second command above. Also, you
   should replace ".cmxs" by ".cma" if you are working with bytcode
   binaries.

### Preludes

Preludes can be passed to Alt-Ergo as follows:

        $ alt-ergo --prelude p.ae --prelude some-path/q.ae [other-options] file.ae

   Alt-Ergo will try to load a local prelude called "p.ae". If this
   fails, Alt-Ergo tries to load it from the default preludes
   directory (run `alt-ergo --where preludes` to see its absolute
   path). You can also provide a relative or an absolute path as shown
   by "some-path/q.ae".

   For instance, the following command-line enables floating-point
   arithmetic reasoning in Alt-Ergo and indicates that the FPA prelude
   should be loaded:

        $ alt-ergo --use-fpa --prelude fpa-theory-2017-01-04-16h00.ae <file.ae>

### Plugins and Preludes directories

As stated above, the `--where` option of `alt-ergo` can be used to get the absolute
path that is searched by default when looking for plugins and preludes that were
given with a relative path. It is useful to know that these two directories are
actually relative to the location of the `alt-ergo` executable, so that the
executable, as well as preludes and plugins, can be relocated.

For instance, on a Linux system, assuming the `alt-ergo` executable is at some path
`some/path/bin/alt-ergo`, theses directories are respectively located at
`some/path/share/alt-ergo/plugins/` and `some/path/share/alt-ergo/preludes/`.
On windows, a binary at path `Z:\some\path\bin\alt-ergo` will look for preludes and
plugins in `Z:\some\path\share\alt-ergo\preludes` and
`Z:\some\path\share\alt-ergo\plugins` respectively.

## Javascript

Alt-Ergo can be compiled in Javascript see the [install section] for more informations.

### Js-node

The Javascript version of Alt-Ergo compatible with node-js is executed with the following command:

        $ node alt-ergo.js  [options] file.<ext>

Note that timeout options and zip files are not supported with this version because of the lack of js primitives.

### Js-worker

A web worker of the alt-ergo solver is available with the command `make js-worker`. It uses Js_of_ocaml Worker's and Lwt. The `data-encoding` library is used to encode and decode messages to/from the worker. Since the messages are in JSon format, the Alt-Ergo worker can be used from any javascript code.

#### Inputs

This web worker takes a json file composed of a list of string representing each line of an input file. This json file can also be composed of an optional worker identifier (integer) and an optional name for the file to solve. The following code shows an example of a such json file :

```
{"filename": "testfile",
 "worker_id": 42,
 "content": [ "goal g : true" ] }
```

The worker also take a Json file that correspond to the options to set in Alt-Ergo, like the following example :

```
{"debug": true,
 "sat_solver": "Tableaux",
 "steps_bound": 1000 }
```

#### Outpus

At the end of solving it returns a Json file corresponding to results, debug informations, etc:

```
{"worker_id": 42, "status": { "Unsat": 0 },
"results": [ "Valid (0.1940) (0 steps) (goal g)", "" ],
"debugs": [ "[Debug][Sat_solver]", "use Tableaux-like solver", "" ],
"model": [ "[all-models] No SAT models found", "" ],
"unsat_core": [ "unsat-core:", "", "", "" ],
"errors": [ "" ],
"warnings": [ "" ],
"statistics": [ [], [] ] }
```

Options and results formats are available in `worker_interface` module. In this module you can also find functions to easily encode inputs and decode outputs.
Look at the `worker_json_example.json` in the ressources `rsc` of the project to learn more.

### Js-worker example

A small example of how to use the Alt-Ergo web worker can be build with the command ```make js-example```. This command also makes the web worker if it has not already been built. It produces a `www` directory with an html page where you can write a small example, run the worker, and see the results. You can also look at the console of your browser to look at the json file send


[install section]: ../Install/index.md
[Lwt]: https://ocsigen.org/lwt/
[js_of_ocaml]: https://ocsigen.org/js_of_ocaml/
[API documentation]: ../API/index.md
[AB-Why3 README]: ../Plugins/ab_why3.md
[Input section]: ../Input_file_formats/index
