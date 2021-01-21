#!/bin/sh -e

# === deploy_doc ===
#
# This script automates the process of updating
# the online documentation by building the html doc,
# checking out gh-pages, and copying all the necessary
# files. Travis will automatically commit the changes
# and push it to the repo

VERSION=$1
ODOC_DIR="odoc"
ODOC_BUILD_DIR="_build/default/_doc/_html/"
SPHINX_BUILD_DIR="_build/sphinx_docs/"

# Cd to the extra dir regardless of where the script was called
git_repo=`git rev-parse --show-toplevel`
cd $git_repo

# Generate documentation, or rather check that it
# has correctly been built.
make doc

# Checkout gh-pages
git fetch origin +gh-pages:gh-pages
git checkout gh-pages

# Create necessary directories if they do not exists
mkdir -p $ODOC_DIR
mkdir -p $ODOC_DIR/$VERSION

# Copy doc to the right locations
cp -r $ODOC_BUILD_DIR/* ./$ODOC_DIR/$VERSION/
cp -r $SPHINX_BUILD_DIR/* ./

# Bypass Jekyll
touch .nojekyll
touch $ODOC_DIR/.nojekyll
touch $ODOC_DIR/$VERSION/.nojekyll

# Clean build artifacts
rm -rf _build
rm Makefile.config
rm -rf rsc/extra/index.html
rm -rf src/bin/text/flags.dune
rm -rf src/lib/util/config.ml
