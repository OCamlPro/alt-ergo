# Usage

## Library

Since version 2.2.0, Alt-Ergo's library is also compiled and installed. See the [API documentation] for more information.

## Run

Alt-Ergo is executed with the following command:

        $ alt-ergo   [options] file.<ext>

The CDCL solver is now the default SAT engine. The command below
allows to enable the old Tableaux-like SAT-solver:

        $ alt-ergo   [options] --sat-solver Tableaux file.<ext>

### Files extensions
Alt-Ergo supports file extensions:
- `.ae`, for its native input language (`.why` and `.mlw` are now depreciated although still accepted)
- `.psmt2`, `.smt2` for (our polymorphic extension of) the SMT-LIB 2
  standard

See the [Input section] for more information about the format of the input files.

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

### Generating models
Alt-Ergo can generates best-effort models in the case it cannot conclude the unsatisfiability of
the context. The model format is a SMT-LIB compatible format, even if you use the native input language.

#### Activation

Model generation is disabled by default. There are two recommended ways to enable it:
- with the native language and the `--dump-models` option, Alt-Ergo tries to produce
  a model after each `check_sat` that returns `I don't known` or
  a counter-example after each `goal` it cannot prove `valid`. Note that both
  `goal` and `check_sat` statements are independent in the native language.

- with the SMT-LIB language and the `--produce-models` option, Alt-Ergo tries to
  produce a model after each `(check-sat)` that returns `unknown`. Models are output
  on demand using the statement `(get-model)`.

  Alternatively, you can enable model generation using the statement
  `(set-option :produce-models true)`.

#### Examples

  - Using the native language in the input file `INPUT.ae`:

  ```
    logic a, b, c : int
    axiom A : a <> c

    check_sat c1: a = b + c
    check_sat c2: a <> b
  ```
  and the command `alt-ergo --dump-models INPUT.ae`, Alt-Ergo produces the
  output models:

  ```
    ; Model for c1
    (
      (define-fun a () Int 2)
      (define-fun b () Int 2)
      (define-fun c () Int 0)
    )
    I don't known

    ; Model for c2
    (
      (define-fun a () Int 2)
      (define-fun b () Int 0)
      (define-fun c () Int 0)
    )
    I don't known
  ```

  ```{admonition} Note

  In this example the model for the statement `check_sat c2` is not a
  model for the statement `check_sat c1` since `check_sat` are independent in
  the native language. The same goes for `goals`.

  ```

  - Using the SMT-LIB language in the input file `INPUT.smt2`:

  ```
    (set-logic ALL)
    (declare-fun a () Int)
    (declare-fun b () Int)
    (declare-fun c () Int)

    (assert (= a (+ b c)))
    (check-sat)
    (get-model)

    (assert (distinct a b))
    (check-sat)

  ```
  and the command `alt-ergo --produce-models INPUT.smt2` produces the output
  ```
    unknown
    (
      (define-fun a () Int 0)
      (define-fun b () Int 0)
      (define-fun c () Int 0)
    )

    unknown
  ```

  ```{admonition} Note

  There is no model printed after the second `(check-sat)` since we
  don't demand it with the statement `(get-model)`.
  ```


  - Alternatively, using the statement `(set-option :produce-models true)`
  ```
   (set-logic ALL)
   (set-option :produce-models true)
   (declare-fun a () Int)
   (declare-fun b () Int)
   (declare-fun c () Int)

   (assert (= a (+ b c)))
   (check-sat)
   (get-model)

  ```
  and the command `alt-ergo INPUT.smt2` produces
  the output model
  ```
  unknown
  (
    (define-fun a () Int 0)
    (define-fun b () Int 0)
    (define-fun c () Int 0)
  )
  ```

  - As a more didactic example, let us imagine while checking the loop invariant
  in the pseudocode below:
  ```
  while i < 5
    invariant i < 5
  do
    i := i + 1
  done
  ```
  we got the SMT-LIB file `INPUT.smt2`:
  ```
  (set-logic ALL)
  (declare-const i Int)
  (assert (and (< i 5) (not (< (+ i 1) 5))))
  (check-sat)
  (get-model)
  ```
  Execute the command
  ```sh
  alt-ergo --produce-models INPUT.smt2
  ```
  We got the output
  ```
  ; File "INPUT.smt2", line 4, characters 1-12: I don't know (0.6689) (2 steps) (goal g_1)

  unknown
  (
    (define-fun i () Int 4)
  )
  ```
  Alt-Ergo tells us that the `(check-sat)` could succeed with `i = 4`. Indeed,
  the loop invariant isn't preserved during the last iteration of the loop and
  the context is satisfiable. Let's fix our specification as follows:
  ```
  while i < 5
      invariant 0 <= i <= 5
  do
      i := i + 1
  end
  ```
  and fix our SMT-LIB input accordingly:
  ```
  (set-logic ALL)
  (declare-const i Int)
  (assert (and (< i 5) (not (<= (+ i 1) 5))))
  (check-sat)
  (get-model)
  ```
  Running the very same command, we got the expected output:
  ```
  ; File "INPUT.smt2", line 4, characters 1-12: Valid (0.5347) (1 steps) (goal g_1)

  unsat
  (error "No model produced.")
  ```
  Our invariant is valid!

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

### Plugins

See the [AB-Why3 README] file for the documentation of the AB-Why3 plugin

The Fm-Simplex plugin can be used as follows:

        $ alt-ergo --inequalities-plugin fm-simplex [other-options] file.<ext>

The `fm-simplex` inequality plugin comes built-in with Alt-Ergo and no further
installation is required. External inequality plugins are supported through the
[Dune-site plugins] mechanism; developers of these plugins must register them
in the `(alt-ergo plugins)`.

### Preludes

Preludes can be passed to Alt-Ergo as follows:

        $ alt-ergo --prelude p.ae --prelude some-path/q.ae [other-options] file.ae

   Alt-Ergo will try to load a local prelude called "p.ae". If this
   fails, Alt-Ergo tries to load it from the default preludes
   directory (run `alt-ergo --where preludes` to see its absolute
   path). You can also provide a relative or an absolute path as shown
   by "some-path/q.ae".

### Plugins and Preludes directories

As stated above, the `--where` option of `alt-ergo` can be used to get the absolute
path that is searched by default when looking for plugins and preludes that were
given with a relative path. It is useful to know that these two directories are
actually relative to the location of the `alt-ergo` executable, so that the
executable, as well as preludes and plugins, can be relocated.

For instance, on a Linux system, assuming the `alt-ergo` executable is at some path
`some/path/bin/alt-ergo`, theses directories are respectively located at
`some/path/lib/alt-ergo/plugins/` and `some/path/lib/alt-ergo/preludes/`.
On windows, a binary at path `Z:\some\path\bin\alt-ergo` will look for preludes and
plugins in `Z:\some\path\lib\alt-ergo\preludes` and
`Z:\some\path\lib\alt-ergo\plugins` respectively.

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
[API documentation]: ../API/index.md
[AB-Why3 README]: ../Plugins/ab_why3.md
[Input section]: ../Input_file_formats/index
[Dune-site plugins]: https://dune.readthedocs.io/en/stable/sites.html#plugins
