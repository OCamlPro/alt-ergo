#!/bin/sh

# === Check_style ===
#
# This script checks that all files in the sources directory
# conform with the style checker in ocpChecker.ml
# It is notably called in the travis scripts

# Cd to the extra dir regardless of where the script was called
git_repo=`git rev-parse --show-toplevel`

cd $git_repo/rsc/extra/ocpchecker

# Compile style checker
make

# List source files to check
files=`find $git_repo/src -regex .*[.]ml[ily]?`

# Counter for the number of files that fail the check
cpt=0

# Loop to check each file
for f in $files ; do
	# only check files that are not untracked and not ignored
	status=`git status $f -s --ignored`
	res=`echo $status | cut -d' ' -f1`
	if ! [ "$res" = "??" ] && ! [ "$res" = "!!" ] ; then
		$git_repo/rsc/extra/ocpchecker/ocp-checker $f
		if ! [ "$?" -eq "0" ] ; then
			cpt=$((cpt+1))
		fi
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
