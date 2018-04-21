#!/bin/sh

files=`find ../sources -regex .*[.]ml[ily]?`

cpt=0

ocamlopt -o ocp-checker ocpChecker.ml

for f in $files ; do
    ./ocp-checker $f
    if ! [ "$?" -eq "0" ] ; then
        cpt=$((cpt+1))
    fi
done

if [ $cpt -eq 0 ] ; then
    exit 0
else
    echo "Some fixes are needed before you can commit"
    exit 1
fi
