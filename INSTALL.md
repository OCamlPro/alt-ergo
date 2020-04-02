# Build and Installation

## Dependencies

External dependencies graph generated with `dune-deps` :

![](docs/deps.png)

To compile the sources, you will need the following libraries :
```
  ocaml >= 4.04.0
  dune >= 1.5
  zarith
  camlzip
  menhir
  ocplib-simplex >= 0.4
  seq
  cmdliner
  stdlib-shims
  psmt2-frontend
```

To compile the GUI you will also need 
```
  lablgtk2
  gtksourceview2
```
You may need superuser permissions to perform the installation.

## Configuration

  1. Configure with `./configure` to generate Makefile.config,
  in order to build everything (lib, parsers, binaries, and GUI).

  2. Alternatively, you can configure with `./configure -prefix
  some-absolute-path-prefix` to add a prefix for installation
  directories. You may also want to use `make gen && cat lib/util/config.ml`
  to see directories where things will be installed.

  3. You can use `./configure <package>` to select which package you
  want to build. `<package>` may be one of: alt-ergo-lib, alt-ergo-parsers,
  alt-ergo, altgr-ergo.

## Build and Install

The steps below will build and install native or bytecode binaries
depending on whether ocamlopt is installed or only ocamlc is detected.

### Everything (binaries, plugins, library, ...)

  1. Compile with `make`

  2. Install with `make install`

  3. Uninstall with `make uninstall` 

### Alt-Ergo library

  1. Compile with `make alt-ergo-lib`

  2. Install with `make install-lib` 

### Alt-Ergo parsers

  1. Compile with `make alt-ergo-parsers`

  2. Install with `make install-parsers` 

### Alt-Ergo binary

  1. Compile with `make alt-ergo`

  2. Install with `make install-bin` 

### AltGr-Ergo binary

  1. Compile with `make altgr-ergo`

  2. Install with `make install-gui` 



## Plugins

The steps below will build and install additional plugins (extension
.cmxs if ocamlopt is installed or .cma if only ocamlc is detected).

### The SatML Plugin

  (satML is now inlined and compiled directly with Alt-Ergo's source code)

### The Fm-Simplex Plugin

  1. Compile with `make fm-simplex`

  2. The Fm-Simplex plugin is currently built and installed
  at the same time as the alt-ergo binary.

### The AB-Why3 parser plugin

  1. Compile with `make AB-Why3`

  2. The AB-Why3 plugin is currently built and installed
  at the same time as the alt-ergo binary.

You can find more information [here](plugins/AB-Why3/README.md)

### The profiler plugin

This plugin has been "inlined" in Alt-Ergo sources.


