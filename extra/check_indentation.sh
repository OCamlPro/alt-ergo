#!/bin/sh

files=`find ../sources -regex .*[.]ml[i]?`

before=`git diff`

for f in $files ; do
    ocp-indent -i $f
done

res=`git diff`

if [ "$res" = "$before" ] ; then
    echo "success: ml(i) files are well indented with ocp-indent"
else
    echo "failure: some ml(i) files are not well indented with ocp-indent"
    echo "<pre>$res</pre>"
    exit 1
fi
