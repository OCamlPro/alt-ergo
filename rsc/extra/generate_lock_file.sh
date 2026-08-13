#!/usr/bin/env bash
set -e
trap cleanup EXIT
export OPAMYES=true
export OPAMSWITCH="$LOCK_SWITCH"

function cleanup() {
  opam switch remove "$LOCK_SWITCH"
}

opam switch create "$LOCK_SWITCH" 5.4.1 --no-switch

opam install --deps-only --with-test --assume-depexts \
  ./alt-ergo-lib.opam \
  ./alt-ergo.opam

opam exec -- dune build @install @runtest -p \
  alt-ergo-lib,alt-ergo

opam lock -w \
  ./alt-ergo-lib.opam \
  ./alt-ergo.opam

opam-ed -i \
  "filter depends ./rsc/extra/filter_depends.sh" \
  -f ./alt-ergo-lib.opam.locked \
  -f ./alt-ergo.opam.locked
