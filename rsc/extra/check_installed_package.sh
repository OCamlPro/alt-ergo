#!/bin/bash

# === check_installed_package.sh ===
#
# This script is intendend to check that install make rules
# install correctly the packages

package=$1
should_fail=$2

test_install () {
    if [ $? -ne 0 ] ; then
        if $should_fail ; then exit 0 ; else exit 1 ; fi ;
    else
        if $should_fail ; then exit 1 ; else exit 0 ; fi ;
    fi;
}

if [ "$package" = "lib" ] || [ "$package" = "parsers" ] ; then
   opam exec -- ocamlfind query alt-ergo-$package ; test_install ;
else
    if [ $package == gui ] ; then
       opam exec -- altgr-ergo --version ; test_install ;
    else
       opam exec -- alt-ergo --version ; test_install ;
    fi
fi
