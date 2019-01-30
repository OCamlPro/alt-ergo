#!/bin/bash -e

# === deploy_doc ===
#
# This script automates the process of updating
# the online documentation by building the html doc,
# checking out gh-pages, and copying all the necessary
# files. Travis will automatically commit the changes
# and push it to the repo

VERSION=$1

# Cd to the extra dir regardless of where the script was called
git_repo=`git rev-parse --show-toplevel`
cd $git_repo

# Generate documentation
(cd sources && make doc)

# Generate version index page
(cd extra && asciidoc index.txt)

# Checkout gh-pages
git checkout gh-pages
git pull origin gh-pages

# Create necessary directories if they do not exists
mkdir -p ./$VERSION

# Copy doc to the right locations
cp extra/index.html ./
cp -r sources/_build/default/_doc/_html/* ./$VERSION/

