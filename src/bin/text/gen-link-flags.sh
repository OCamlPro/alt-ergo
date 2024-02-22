#!/bin/sh

set -ue

LINK_MODE="$1"
OS="$2"
FLAGS=
CCLIB=

case "$LINK_MODE" in
  dynamic)
    ;; # No extra flags needed
  static)
    case "$OS" in
      linux)
        CCLIB="-static -no-pie";;
      *)
        echo "No known static compilation flags for '$OS'" >&2
        exit 1
    esac;;
  mixed)
    FLAGS="-noautolink"
    CCLIB="-lstdcompat_stubs -lcamlzip -lnums -lzarith -lcamlstr -lunix -lz"
    LIBS="gmp"
    case "$OS" in
      linux)
        for lib in $LIBS; do
          CCLIB="$CCLIB -l$lib"
        done;;
      macosx)
        for lib in $LIBS; do
          if [[ $lib == lib* ]]; then
            archive="$lib.a"
          else
            archive="lib$lib.a"
          fi
          CCLIB="$CCLIB $(pkg-config $lib --variable libdir)/$archive"
        done;;
      *)
        echo "No known mixed compilation flags for '$OS'" >&2
        exit 1
    esac;;

  *)
    echo "Invalid link mode '$LINK_MODE'" >&2
    exit 2
esac

echo '('
echo ' -linkall'
for f in $FLAGS; do echo " $f"; done
for f in $CCLIB; do echo " -cclib $f"; done
echo ')'
