#!/bin/sh

# === check_indentation ===
#
# This script checks indentation of files, using the in-place
# option of ocamlformat.
# It is notably called in the travis scripts

# Perform all actions relative to the git root
git_repo=`git rev-parse --show-toplevel`

# List source files to check
# Keep this pattern in sync with the pre-commit hook
files=`find $git_repo/src -regex .*[.]ml[i]?`

# Save the state before ocamlformat
before=`git diff`

# Counter for the number of files checked
cpt=0

# Loop to check each file
for f in $files ; do
	ocamlformat -i $f
	cpt=$((cpt+1))
done

# Save the state after ocamlformat
res=`git diff`

# Exit
echo "checked $cpt files"
if [ "$res" = "$before" ] ; then
	echo "success: all ml(i) files are well indented with ocamlformat"
else
	echo "failure: some ml(i) files are not well indented with ocamlformat"
	echo "<pre>$res</pre>"
	echo "Some fixes are needed before you can commit"
	exit 1
fi
