#!/bin/sh
set -eu

# === check_javascript ===
#
# This script is intendend to check that alt-ergo-js builds
# and run correctly with nodejs

# Be sure of where we are, and initialize some variables
git_repo=`git rev-parse --show-toplevel`
local_install_dir=$1

# Cd into the root project directory
cd $git_repo

# Install Alt-ergo-js deps here since this deps can't be made 
# for all Alt-Ergo's supported version of OCaml (< 4.07).
opam pin add --no-action .
opam install --deps-only alt-ergo-lib alt-ergo-parsers alt-ergo-js ||
 ( opam update &&
   opam install --deps-only alt-ergo-lib alt-ergo-parsers alt-ergo-js)
opam install alt-ergo-lib alt-ergo-parsers

# Configure using the local installation directory
./configure --prefix=$local_install_dir alt-ergo-js

# Check that the worker targets work
echo "=+= [make js-worker] building ... =+="
make js-worker

# Check that the small web example targets work
echo "=+= [make js-example] building ... =+="
make js-example

# Check that the node targets work
echo "=+= [make js-node] building ... =+="
make js-node

# Run the tests
cd $git_repo/non-regression
./run_valid.sh "node ../alt-ergo.js" "0" false
./run_invalid.sh "node ../alt-ergo.js" "0" false
