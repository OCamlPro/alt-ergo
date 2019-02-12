#!/bin/sh

# === check_indentation ===
#
# This script checks indentation of files, using the in-place
# option of ocp-indent.
# It is notably called in the travis scripts

# Perform all actions relative to the git root
git_repo=`git rev-parse --show-toplevel`
files=`find $git_repo/sources -regex .*[.]ml[i]?`

before=`git diff`
cpt=0

for f in $files ; do
    ocp-indent -i $f
    cpt=$((cpt+1))
done

res=`git diff`

echo "checked $cpt files"
if [ "$res" = "$before" ] ; then
    echo "success: all ml(i) files are well indented with ocp-indent"
else
    echo "failure: some ml(i) files are not well indented with ocp-indent"
    echo "<pre>$res</pre>"
    exit 1
fi
