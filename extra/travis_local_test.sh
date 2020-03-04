#!/bin/sh -e

# === travis local test ===
#
# This script is called in the travis local test
# Its goal is to check:
# - that all opam packages of alt-ergo correctly build
# - that the produces binary is correct wrt. non-regression tests
# - that the lib is usable as expected

LOCAL_DIR=$1

# Cd to the extra dir regardless of where the script was called
git_repo=`git rev-parse --show-toplevel`

# Install alt-ergo packages
$git_repo/extra/check_makefile.sh $LOCAL_DIR

# Run the non-regression tests
$git_repo/extra/non_regression.sh

# Test the lib usage
$git_repo/extra/test_lib.sh $LOCAL_DIR/lib/alt-ergo-lib
