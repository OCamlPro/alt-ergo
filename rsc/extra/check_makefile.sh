#!/bin/bash -e

# === check_makefile ===
#
# This script is intendend to check that alt-ergo builds
# and install correctly when the makefile is called directly

# Be sure of where we are, and initialize some variables
git_repo=`git rev-parse --show-toplevel`
local_install_dir=$1

# Cd into the root project directory
cd $git_repo

# Configure using the local installation directory
./configure --prefix=$local_install_dir

# Check that the makefile targets work
echo "=+= [check_makefile.sh] building and installing ... =+="
make lib
make bin
make gui
make plugins

make alt-ergo-lib
make install-lib

make alt-ergo-parsers
make install-parsers

make alt-ergo
make install-bin

make altgr-ergo
make install-gui

make clean

# WARNING: the next lines are commented because it made the output hard to read

# Log the result of installation
#echo "=+= [check_makefile.sh] installed files in '$local_install_dir' =+="
#ls -R $local_install_dir
