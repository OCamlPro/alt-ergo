#!/bin/sh

#
# This script should be put in directory example of why3 git
# to generate VCs for alt-ergo and SMT2 (z3 driver)
#

rm -f why3-benchs

rm -rf in_progress
rm -rf tests
rm -rf check-builtin
rm -rf hoare_logic/draft

run_why3_prove(){
    file="$1"
    include="$2"
    driver="$3"
    echo running \"why3 prove\" on file \"$file\" with include \"$include\"
    why3 prove $file $include -a split_all_full -D $driver -o why3-benchs/$driver
}

for driver in alt_ergo z3 ; do

    mkdir -p why3-benchs/$driver

    echo "\n=====\nGenerating benchs for driver $driver\n=====\n"

    for f in `find . -name why3session.xml`; do
        d=`dirname $f`
        dd=`dirname $d`
        echo 
        echo "file $d.[mlw|why]"
        if [ -e ${d}.mlw ]; then
            run_why3_prove "${d}.mlw" "" $driver
            if ! [ "$?" -eq "0" ]; then
                run_why3_prove "${d}.mlw" "-L $dd" $driver
                if ! [ "$?" -eq "0" ]; then
                    echo ">>>> running \"why3 prove\" on ${d}.mlw failed\n"
                fi
            fi
        else
            if [ -e ${d}.why ]; then
                run_why3_prove "${d}.why" "" $driver
                if ! [ "$?" -eq "0" ]; then
                    run_why3_prove "${d}.why" "-L $dd" $driver
                    if ! [ "$?" -eq "0" ]; then
                        echo ">>>> running \"why3 prove\" on ${d}.why failed\n"
                    fi
                fi
            else
                echo ">>>> no .mlw or .why file for $d, skip \"$d\"...\n"
            fi
        fi
    done

    ls why3-benchs/$driver/* | wc -l

done

git checkout in_progress
git checkout tests
git checkout check-builtin
git checkout hoare_logic/draft
