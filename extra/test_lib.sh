#!/bin/bash -e

# === test_lib ===
#
# This script checks that the alt ergo library is
# usable in practice. To do so, it tries and compile
# a small example using the lib. This example is in the
# file sources/examples/lib_usage.ml


# Some boilerplate
git_repo=`git rev-parse --show-toplevel`
lib_path=$1

# Log some concrete values used in the test
echo "=+= [travis.sh] build and test library example ... =+="
echo "which alt-ergo == `which alt-ergo`"
echo "alt-ergo -version == `alt-ergo -version`"
echo "path to lib == $lib_path"
x=`ls $lib_path`
echo "content of lib == $x"

# Compile the lib_usage caml file
cd $git_repo/sources/examples
ocamlopt -o lib_usage \
  -I `ocamlfind query num` \
  -I `ocamlfind query zarith` \
  -I `ocamlfind query ocplib-simplex` \
  -I `ocamlfind query psmt2-frontend` \
  -I `ocamlfind query camlzip` \
  -I $lib_path \
  nums.cmxa zarith.cmxa ocplibSimplex.cmxa psmt2Frontend.cmxa \
  unix.cmxa str.cmxa zip.cmxa dynlink.cmxa \
  AltErgoLib.cmxa lib_usage.ml

# Execute the lib usage test
./lib_usage

