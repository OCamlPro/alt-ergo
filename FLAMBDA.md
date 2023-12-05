# FLAMBDA

This document describes how to install Alt-Ergo with FLAMBDA 1 and 2 with opam.
Note that the FLAMBDA 2 instructions are incomplete: feel free to fix them if
you manage to install alt-ergo with it.

We first describe how to set up an opam switch with flambda, then how to
configure the compilation procedure with flambda

## Install with FLAMBDA

### FLAMBDA 1

First, create a fresh empty switch and install the base

```
$ opam switch create flambda1 --empty
$ eval $(opam env)
$ opam install ocaml-variants.4.14.1+options ocaml-option-flambda
$ opam switch set-invariant ocaml.4.14.1
```

If alt-ergo depends on a specific version of dolmen, do not forget about pinning
the right dolmen version before installing the dependencies.

`$ opam install . --deps-only`

Finally, you can build with `m bin`.

### FLAMBDA 2

To install Alt-Ergo with FLambda, you first need to have:
- ocaml.4.14.1 installed on your current opam switch;
- [opam-custom-install](https://gitlab.ocamlpro.com/louis/opam-custom-install) installed on any switch.

Create a new switch in which we will install the compiler:

```
$ opam switch create flambda-backend --empty --repositories=flambda2=git+https://github.com/ocaml-flambda/flambda2-opam.git,default
$ opam switch THE_4.14.1_SWITCH
```

Fetch the `flambda-backend` repository:

```
$ git clone https://github.com/ocaml-flambda/flambda-backend.git
$ cd flambda-backend
```

Once in the flambda directory, configure the build directory:

```
$ autoconf
$ ./configure --prefix=PATH_TO_THE_EMPTY_FLAMBDA_SWITCH --enable-middle-end=flambda2 --enable-legacy-library-layout
```

The last option `--enable-legacy-library-layout` is required for projects on the
4.14.1 OCaml version (and probably 4.14.0 too) because of the `Unix` module
dependency. Then, you can build the project and install it on the
flambda-backend switch.

```
$ make _install
$ opam switch flambda-backend
$ opam custom-install ocaml-variants.4.14.1+flambda2 -- make install_for_opam
$ opam reinstall --forget-pending
$ opam install ocaml.4.14.1
```

## Build with flambda

When you build alt-ergo, you can set compilation options through the
`OCAMLPARAM` variable. Here is an example on how to set options to the
compiler to build alt-ergo with extreme optimization:

```
$OCAMLPARAM='_,rounds=5,O3=1,inline=100,inline-max-unroll=5' make bin
```

You can find an exhaustive documentation
[here](https://v2.ocaml.org/manual/flambda.html).
You may also want to use `ulimit` if you plan to use your computer while
compiling.

NB: this variable can also be set to the `opam install` commands installing the
dependencies to optimize them as well.