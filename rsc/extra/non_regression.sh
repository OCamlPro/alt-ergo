#!/bin/bash -e

# === non_regression ===
#
# This script runs the non_regression tests using the
# alt-ergo binary found in the PATH

# Cd to the non-regression directory
git_repo=`git rev-parse --show-toplevel`
cd $git_repo/non-regression

# Log some practical info
echo "=+= [travis.sh] non-regression tests ... =+="
echo "which alt-ergo == `which alt-ergo`"
echo "alt-ergo --version == `alt-ergo --version`"

# Run the tests
sh ./run_valid.sh "alt-ergo" "1"
sh ./run_invalid.sh "alt-ergo" "1"
