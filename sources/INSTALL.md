## Build and Installation

  You need OCaml >= 4.04.0, zarith, camlzip, menhir and ocplib-simplex >= 0.4
  to compile the sources. You need LablGtk2 and the widget
  GSourceView2 to compile the GUI. You may need superuser permissions
  to perform the installation.

#### Common Steps

  1. If a configure file is not distributed with the sources, then
  run "autoconf"

  2. Configure with "./configure" to generate Makefile.configurable

  3. Alternatively, you can configure with "./configure -prefix
  some-absolute-path-prefix" to add a prefix for installation
  directories. You may also want to use "make show-dest-dirs" to see
  directories where things will be installed.

The steps below will build and install native or bytecode binaries
depending on whether ocamlopt is installed or only ocamlc is detected.

#### Everything (binaries, plugins, ...)

  1. Compile with "make"

  2. Install with "make install"
 
  3. Uninstall with "make uninstall"

#### Alt-Ergo binary

  1. Compile with "make alt-ergo"

  2. Install with "make install-ae"
 
#### AltGr-Ergo binary

  1. Compile with "make gui"
  
  2. Install with "make install-gui"


The steps below will build and install additional plugins (extension
.cmxs if ocamlopt is installed or .cma if only ocamlc is detected).

#### The SatML Plugin

  (satML is now inlined and compiled directly with Alt-Ergo's source code)

#### The Fm-Simplex Plugin

  1. Compile with "make fm-simplex"

  2. Install with "make install-fm-simplex"

#### The profiler plugin

This plugin has been "inlined" in Alt-Ergo sources.

## Usage

- Alt-Ergo and AltGr-Ergo are executed with the following commands,
  respectively:

        $ alt-ergo   [options] file.why
        $ altgr-ergo [options] file.why

The CDCL solver is now the default SAT engine. The commands below
allow to enable the old Tableaux-like SAT-solver:

        $ alt-ergo   [options] -sat-solver Tableaux file.why
        $ altgr-ergo [options] -sat-solver Tableaux file.why

- The Fm-Simplex plugin can be used as follows:

        $ alt-ergo -inequalities-plugin fm-simplex-plugin.cmxs [other-options] file.why
        $ alt-ergo -inequalities-plugin some-path/fm-simplex-plugin.cmxs [other-options] file.why

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
