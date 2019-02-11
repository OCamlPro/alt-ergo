## Build and Installation

  You need OCaml >= 4.04.0, zarith, camlzip, menhir, ocplib-simplex >=
  0.4 and psmt2-frontend library to compile the sources. You need
  LablGtk2 and the widget GSourceView2 to compile the GUI. You may
  need superuser permissions to perform the installation.

#### Configuration

  1. Configure with "./configure" to generate Makefile.config,
  in order to build everything (lib, parsers, binaries, and GUI).

  2. Alternatively, you can configure with "./configure -prefix
  some-absolute-path-prefix" to add a prefix for installation
  directories. You may also want to use "make gen && cat lib/util/config.ml"
  to see directories where things will be installed.

  3. You can use "./configure <package>" to select which package you
  want to build. "<package>" may be one of: alt-ergo-lib, alt-ergo-parsers,
  alt-ergo, altgr-ergo.

The steps below will build and install native or bytecode binaries
depending on whether ocamlopt is installed or only ocamlc is detected.

#### Everything (binaries, plugins, library, ...)

  1. Compile with "make"

  2. Install with "make install"

  3. Uninstall with "make uninstall"

#### Alt-Ergo library

  1. Compile with "make alt-ergo-lib"

  2. Install with "make install-lib"

#### Alt-Ergo parsers

  1. Compile with "make alt-ergo-parsers"

  2. Install with "make install-parsers"

#### Alt-Ergo binary

  1. Compile with "make alt-ergo"

  2. Install with "make install-bin"

#### AltGr-Ergo binary

  1. Compile with "make altgr-ergo"

  2. Install with "make install-gui"


The steps below will build and install additional plugins (extension
.cmxs if ocamlopt is installed or .cma if only ocamlc is detected).

#### The SatML Plugin

  (satML is now inlined and compiled directly with Alt-Ergo's source code)

#### The Fm-Simplex Plugin

  1. Compile with "make fm-simplex"

  2. The Fm-Simplex plugin is currently built and installed
  at the same time as the alt-ergo binary.

#### The profiler plugin

This plugin has been "inlined" in Alt-Ergo sources.


## Usage

Alt-Ergo supports file extensions:
- `.why`, `.mlw`, `.ae` for its native input language
- `.psmt2`, `.smt2` for (our polymorphic extension of) the SMT-LIB 2
  standard

- Alt-Ergo and AltGr-Ergo are executed with the following commands,
  respectively:

        $ alt-ergo   [options] file.<ext>
        $ altgr-ergo [options] file.<ext>

The CDCL solver is now the default SAT engine. The commands below
allow to enable the old Tableaux-like SAT-solver:

        $ alt-ergo   [options] -sat-solver Tableaux file.<ext>
        $ altgr-ergo [options] -sat-solver Tableaux file.<ext>

- The Fm-Simplex plugin can be used as follows:

        $ alt-ergo -inequalities-plugin fm-simplex-plugin.cmxs [other-options] file.<ext>
        $ alt-ergo -inequalities-plugin some-path/fm-simplex-plugin.cmxs [other-options] file.<ext>

   Alt-Ergo will try to load a local plugin called
   "fm-simplex-plugin.cmxs". If this fails, Alt-Ergo tries to load it
   from the default plugins directory (run "alt-ergo -where plugins"
   to see its absolute path). You can also provide a relative or an
   absolute path as shown by the second command above. Also, you
   should replace ".cmxs" by ".cma" if you are working with bytcode
   binaries.

- Preludes can be passed to Alt-Ergo as follows:

        $ alt-ergo -prelude p.why -prelude some-path/q.why [other-options] file.why

   Alt-Ergo will try to load a local plugin called "p.why". If this
   fails, Alt-Ergo tries to load it from the default preludes
   directory (run "alt-ergo -where preludes" to see its absolute
   path). You can also provide a relative or an absolute path as shown
   by "some-path/q.why".

   For instance, the following command-line enables floating-point
   arithmetic reasoning in Alt-Ergo and indicates that the FPA prelude
   should be loaded:

   $ alt-ergo -use-fpa -prelude fpa-theory-2017-01-04-16h00.why <file.why>

- Since version 2.2.0, Alt-Ergo's library is also compiled and
  installed. A small example using the API is given here:
  "examples/lib_usage.ml"
