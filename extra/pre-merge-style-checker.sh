#!/bin/sh -e

# === pre-merge-style-checker ===
#
# This script checks that all files in the sources directory
# conform with the style checker in ocpChecker.ml
# It is notably called in the travis scripts


# Cd to the extra dir regardless of where the script was called
git_repo=`git rev-parse --show-toplevel`
cd $git_repo/extra

# Compile style checker
ocamlfind ocamlopt -o ocp-checker -linkpkg -package stdlib-shims ocpChecker.ml

# List source files to check
files=`find ../sources -regex .*[.]ml[ily]?`

# Counter for the number of files that fail the check
cpt=0

# Loop to check each file
for f in $files ; do
    $git_repo/extra/ocp-checker $f
    if ! [ "$?" -eq "0" ] ; then
        cpt=$((cpt+1))
    fi
done

# Exit
if [ $cpt -eq 0 ] ; then
    echo "All files have correct style"
    exit 0
else
    echo "Some fixes are needed before you can commit"
    exit 1
fi
