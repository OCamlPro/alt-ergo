#!/usr/bin/env bash
set -euo pipefail
export LOCKED_SWITCH="alt-ergo-locked"
export OPAMYES=true
export OPAMSWITCH="$LOCKED_SWITCH"

function check_switch_available() {
  opam list >/dev/null 2>&1
}

if check_switch_available; then
  cat << EOF
The switch $LOCKED_SWITCH already exists. Please remove it to run the script
or override the value of the environment variable \$LOCKED_SWITCH.
EOF
  exit 1
fi

opam switch create "$LOCKED_SWITCH" 5.4.1 --no-switch

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
