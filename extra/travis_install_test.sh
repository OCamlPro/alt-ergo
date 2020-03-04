#!/bin/sh -e

# === travis installation test ===
#
# This script is called in the travis installation test
# Its goal is to check:
# - that all opam packages of alt-ergo correctly install using opam
# - that the produces binary is correct wrt. non-regression tests
# - that the lib is usable as expected

# Cd to the extra dir regardless of where the script was called
git_repo=`git rev-parse --show-toplevel`
cd $git_repo

# Install alt-ergo packages
opam install alt-ergo-lib alt-ergo altgr-ergo

# Run the non-regression tests
$git_repo/extra/non_regression.sh

# Test the lib usage
$git_repo/extra/test_lib.sh `ocamlfind query alt-ergo-lib`
