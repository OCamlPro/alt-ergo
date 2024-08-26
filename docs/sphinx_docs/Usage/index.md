# Usage

## Command-line

Alt-Ergo is executed with the following command:

```console
$ alt-ergo   [options] file.<ext>
```

The CDCL solver is now the default SAT engine. The command below
allows to enable the old Tableaux-like SAT-solver:

```console
$ alt-ergo   [options] --sat-solver Tableaux file.<ext>
```

### Output
The results of an Alt-ergo's execution have the following form :
```
File "<path_to_file>/<filename>", line <l>, characters <n-m>: <status> (<time in seconde>) (<number of steps> steps) (goal <name of the goal>)
```
The status can be `Valid`, `Invalid` or `I don't know`. If the input file is in
the SMT-LIB 2 format the status will be either `unsat`, `sat`, `unknown`.
You can force the status to be print in the SMT-LIB 2 form with the option `--output smtlib2`.

```{admonition} Note
When Alt-Ergo tries to prove a `goal` (with the native input language), it
actually tries to prove the unsatisfiability of its negation. That is
why you get `unsat` answer as an SMT-LIB 2 format output while proving a `Valid`
goal. The same goes for `Invalid` and `sat`.
```

### Files extensions
Alt-Ergo supports file extensions:
- `.psmt2`, `.smt2` for (our polymorphic extension of) the SMT-LIB 2
  standard
- `.ae`, for its native input language (`.why` and `.mlw` are now deprecated although still accepted)
- `.psmt2.zip`, `.smt2.zip` and `.ae.zip` for compressed files

See the [SMT-LIB language] and [Alt-ergo native language] sections for more information about the format of the input files.

### Frontend option

The `--frontend` option lets you select the frontend used to parse and type the input file. Since version 2.5.0,
Alt-Ergo integrates two frontends:
- The `dolmen` frontend is the default frontend, powered by the
  [Dolmen](https://github.com/Gbury/dolmen) library.  The native and SMT-LIB
  languages are both supported by this frontend.
- The `legacy` frontend is the historical frontend of Alt-Ergo supporting the
  native language. You can select it with the `--frontend legacy` option. The
  legacy frontend is deprecated, and will be removed in a future release.

```{admonition} Note

The `legacy` frontend has limited support for the SMT-LIB language, but many
SMT-LIB features will not work with the `legacy` frontend. Use the (default)
`dolmen` frontend for SMT-LIB inputs.
```

### Preludes

Preludes can be passed to Alt-Ergo as follows:

```console
$ alt-ergo --prelude p.ae --prelude some-path/q.ae [other-options] file.ae
```

   Alt-Ergo will try to load a local prelude called "p.ae". If this
   fails, Alt-Ergo tries to load it from the default preludes
   directory (run `alt-ergo --where preludes` to see its absolute
   path). You can also provide a relative or an absolute path as shown
   by "some-path/q.ae".

### Strict mode
Alt-Ergo supports extensions that are not part of the SMT-LIB standard. For
convenience, some of these extensions are enabled by default. Since the
version 2.6.0, the flag `--strict` disables the extensions:
- MaxSMT extension for the optimization

We plan to disable more nonstandard extensions with this flag in futur versions.
## Library

Since version 2.2.0, Alt-Ergo's library is also compiled and installed. See the
[API documentation] (also available [on ocaml.org](https://ocaml.org/p/alt-ergo-lib/latest/doc/index.html))
for more information.

## Javascript

Alt-Ergo can be compiled in Javascript see the [install section] for more informations.

### Js-node

The Javascript version of Alt-Ergo compatible with node-js is executed with the following command:

```console
$ node alt-ergo.js  [options] file.<ext>
```

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

#### Outputs

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

A small example of how to use the Alt-Ergo web worker can be build with the command ```make js-example```. This command also makes the web worker if it has not already been built. It produces a `www` directory with an html page where you can write a small example, run the worker, and see the results. You can also look at the console of your browser to look at the json file sent

[install section]: ../Install/index.md
[Lwt]: https://ocsigen.org/lwt/
[js_of_ocaml]: https://ocsigen.org/js_of_ocaml/
[API documentation]: ../API/index
[AB-Why3 README]: ../Plugins/ab_why3.md
[Alt-ergo native language]: ../Alt_ergo_native/index
[SMT-LIB language]: ../SMT-LIB_language/index
[Dune-site plugins]: https://dune.readthedocs.io/en/stable/sites.html#plugins
