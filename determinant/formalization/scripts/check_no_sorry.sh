#!/usr/bin/env bash
# check_no_sorry.sh <build log>: fail if the build log reports a declaration that uses `sorry`
# anywhere outside CN1Challenges/ (the challenge statement is a `sorry` by design, as Comparator
# requires), or mentions sorryAx.
set -uo pipefail
f=${1:?usage: check_no_sorry.sh <lake build log>}
hits=$(grep -E "declaration uses .sorry." "$f" | grep -vE "^(warning: )?(\./)*CN1Challenges/" || true)
if [ -n "$hits" ]; then
  echo "FAIL: sorry outside CN1Challenges:"; printf '%s\n' "$hits"; exit 1
fi
if grep -q 'sorryAx' "$f"; then
  echo "FAIL: sorryAx in the build log"; exit 1
fi
echo "OK: the only sorry warnings are in CN1Challenges ($(grep -cE "declaration uses .sorry." "$f" || true) of them)"
