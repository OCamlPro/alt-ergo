# Alt-Ergo in JavaScript

These available artifacts are:
- A JavaScript version of the Alt-Ergo binary named `alt-ergo.js`.
- A web worker and an example using `js_of_ocaml` and `Lwt`.

> The `--timeout` option is ignored due to a lack of JavaScript primitives.
> Zip files are not recognized as file extensions.

# Worker inputs and outpus

The Web worker expects a JSON file containing a list of strings, where
each string represents a line of an input file.

This JSON file can also include:
- An optional worker identifier (integer),
- An optional filename.

Example:
```json
[
  {
    "filename": "testfile",
    "worker_id": 42,
    "content": ["goal g : true"]
  }
]
```

The worker also accepts a JSON file to configure `Alt-Ergo`. For instance,
```json
[
  {
    "debug": true,
    "sat_solver": "Tableaux",
    "steps_bound": 1000
  }
]
```

Upon completion, it returns a JSON file containing the results, debugging
information, and statistics:
```json
[
  {
    "worker_id": 42,
    "status": { "Unsat": 0 },
    "results": [ "Valid (0.1940) (0 steps) (goal g)", "" ],
    "debugs": [ "[Debug][Sat_solver]", "use Tableaux-like solver", "" ],
    "model": [ "[all-models] No SAT models found", "" ],
    "unsat_core": [ "unsat-core:", "", "", "" ],
    "errors": [ "" ],
    "warnings": [ "" ],
    "statistics": [ [], [] ],
 }
]
 ```

The option and result formats are defined in the
`Worker_interface.worker_interface` module. For more details, see
`worker_json_example.json` in the resource directory `rsc`.

# Installation

To install the `Alt-Ergo` JavaScript artifacts, simply install the `alt-ergo-js`
opam package. The artifacts will be available in `SHARE/alt-ergo-js`, where
`SHARE` refers to the share directory of your current opam switch.

The JavaScript artifacts require at least NodeJS 16.9.0.
To execute Alt-Ergo JavaScript, use the following command:
```console
node SHARE/alt-ergo-js/alt-ergo.js <options> <input_files>
```
and to serve the example, type:
```console
python -m http.server -d SHARE/alt-ergo-js
```

# Setup development environment

Use `make dev-switch` to create a local opam switch with all necessary
dependencies. Then, run `make js` to compile the JavaScript artifacts into the
`www` directory at the project root.

To execute Alt-Ergo JS locally:
```console
node www/alt-ergo.js <options> <input_file>
```
To serve the example:
```console
python -m http.server -d www
```
