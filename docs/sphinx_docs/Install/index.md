# Installation

This page explains how to install both the Alt-Ergo releases and the
development versions. If you are interested in contributing to this project,
please refer to the developer documentation.

## Releases

### Installing via opam

The recommended way to install Alt-Ergo releases is throught the OCaml package
manager [opam]. Simply run:
```console
opam install alt-ergo
```
to install the latest Alt-Ergo release in the current switch.

A free version of Alt-Ergo is also available on opam. To install it, run:
```console
opam install alt-ergo-free
```

### Installing via GitHub releases (Linux and macOS)

For convenience, binary releases for Linux and macOS (amd64 and arm64) of
Alt-Ergo are provided on the [GitHub release page](https://github.com/OCamlPro/alt-ergo/releases).
These binary releases are statically linked and very portable.
They are distributed under the same licensing restrictions as the source code.

## Development versions

### Installing via opam
To install the development version of Alt-Ergo from a cloned Git repository,
run at the root of the repository:
```
opam install .
```
This installs `alt-ergo`, `alt-ergo-lib` and all their dependencies in the
current switch.

### Installing via Dune
If you prefer install Alt-Ergo binary in a specific prefix directory [DIR], use
the following commands:
```
make deps
make bin
dune install -p alt-ergo --prefix DIR
```

### Plugins

The steps below will build and install additional plugins.

#### The Fm-Simplex Plugin

  1. Compile with `make fm-simplex`

  2. The Fm-Simplex plugin is currently built and installed
  at the same time as the alt-ergo binary.

#### The AB-Why3 parser plugin

This plugin was deprecated in Alt-Ergo 2.6.0 and removed in Alt-Ergo
2.7.0.

[opam]:  https://opam.ocaml.org/
[here]: https://packages.debian.org/buster/alt-ergo
