#!/bin/sh -e

# === travis documentation test ===
#
# This script is called in the travis documentation test
# Its goal is to check that the documentation builds
# without warnings or errors

LOGFILE=doc.log

# Cd to the extra dir regardless of where the script was called
git_repo=`git rev-parse --show-toplevel`
cd $git_repo

# Call the configure script
echo "Calling configure script..."
./configure

# Build the ocaml documentation and record the log
echo "Building OCaml documentation..."
make odoc | tee $LOGFILE

# NOTE: currently dune has no option to fail on odoc warnings,
#       so we use a dirty grep to look for errors in the log
echo "Checking for warnings or errors during ocaml documentation building..."
! grep File $LOGFILE

# remove artifact log file
rm -f $LOGFILE

# Build the sphinx documentation and record the log
echo "Building Sphinx documentation..."
make sphinx-doc 2> $LOGFILE

# NOTE: sphinx-build does not exit with error
#       if an error occurs during the build
echo "Checking for errors during sphinx documentation building..."
! grep Error $LOGFILE

# remove artifact log file
rm -f $LOGFILE

# exit nicely
echo "All good"
