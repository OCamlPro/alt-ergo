# Installation

## From a package manager

Alt-ergo is available on [opam], the ocaml package manager with the following command :
```
opam install alt-ergo
```

This two command will install the Alt-ergo library `alt-ergo-lib` and the parsers `alt-ergo-parsers`, as well as other librairies detailled in [dependencies](#dependencies).

### On Debian

Alt-ergo is also available in the debian package manager [here]. You can install it with the following command :

```
sudo apt install alt-ergo
```

## From sources

### Dependencies

External dependencies graph generated with `dune-deps` (use `make archi` for source files dependencies):

![](deps.png)

To compile the sources, you will need the following libraries :
```
  ocaml >= 4.08.0
  dune >= 3.0
  zarith >= 1.4
  camlzip
  menhir
  ocplib-simplex >= 0.5
  seq
  cmdliner
  stdlib-shims
  psmt2-frontend
```

You can install dependencies using:

```
$ make deps
```

and create a development switch with:

```
$ make dev-switch
```

### Build and Install

The steps below will build and install native or bytecode binaries
depending on whether ocamlopt is installed or only ocamlc is detected.

Note: these are somewhat obsolete; nowadays you can just use `dune`

#### Everything (binaries, plugins, library, ...)

  1. Compile with `make`

  2. Install with `make install-all`

  3. Uninstall with `make uninstall-all`

#### Alt-Ergo library

  1. Compile with `make alt-ergo-lib`

  2. Install with `make install-lib`

#### Alt-Ergo parsers

  1. Compile with `make alt-ergo-parsers`

  2. Install with `make install-parsers`

#### Alt-Ergo binary

  1. Compile with `make alt-ergo`

  2. Install with `make install-bin`

#### Alt-Ergo with Nodejs

You can install dependencies using:

```
$ make js-deps
```

  1. Compile with `make js-node`

For this build rule you will need the following aditional libraries :
```
js_of_ocaml between 4.0.1 and 5.0.1
zarith_stubs_js
```

#### Alt-Ergo web worker

  1. Compile with `make js-worker`

For this build rule you will need the following aditional libraries :
```
js_of_ocaml between 4.0.1 and 5.0.1
js_of_ocaml-lwt
zarith_stubs_js
data-encoding
```

#### Alt-Ergo web worker small example

  1. Compile with `make js-example`

This command create a `www/` directory in which you can find a small js example running in the `index.html` file

For this build rule you will need the following aditional libraries :
```
js_of_ocaml between 4.0.1 and 5.0.1
js_of_ocaml-lwt
js_of_ocaml-ppx
lwt_ppx
zarith_stubs_js
data-encoding
```

### Plugins

The steps below will build and install additional plugins (extension
.cmxs if ocamlopt is installed or .cma if only ocamlc is detected).

#### The SatML Plugin

 satML is now inlined and compiled directly with Alt-Ergo's source code

#### The Fm-Simplex Plugin

  1. Compile with `make fm-simplex`

  2. The Fm-Simplex plugin is currently built and installed
  at the same time as the alt-ergo binary.

#### The AB-Why3 parser plugin

  1. Compile with `make AB-Why3`

  2. The AB-Why3 plugin is currently built and installed
  at the same time as the alt-ergo binary.

You can find more information in the [AB-Why3 README]

#### The profiler plugin

This plugin has been "inlined" in Alt-Ergo sources.


[AB-Why3 README]: ../Plugins/ab_why3.md
[opam]:  https://opam.ocaml.org/
[here]: https://packages.debian.org/buster/alt-ergo
