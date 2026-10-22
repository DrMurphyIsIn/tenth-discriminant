#!/usr/bin/env bash
# check_no_sorry.sh <build log>: check the log of `lake build ELEM CN1 CN1Challenges`.
#
# Passes exactly when the log reports a successful build and contains exactly one line that mentions `sorry`, and that line
# is the warning for the challenge statement:
#   warning: CN1Challenges/ClassNumberOne.lean:<line>:<col>: declaration uses `sorry`
# (the challenge is a `sorry` by design, as Comparator requires). It fails closed: on a missing or empty log, a log without
# "Build completed successfully", a log with no sorry warning at all (so the challenge was not built), a second sorry
# warning anywhere (including a second one in CN1Challenges/), any other line that mentions sorry, and any mention of
# sorryAx. scripts/test_checks.sh runs this script over the fixtures in scripts/fixtures/.
set -uo pipefail
f=${1:?usage: check_no_sorry.sh <lake build log>}
[ -s "$f" ] || { echo "FAIL: missing or empty build log: $f"; exit 1; }
grep -q 'Build completed successfully' "$f" || { echo "FAIL: the log does not report a successful build"; exit 1; }
if grep -q 'sorryAx' "$f"; then
  echo "FAIL: sorryAx in the build log"; exit 1
fi
hits=$(grep -i 'sorry' "$f" || true)
n=$(printf '%s' "$hits" | grep -c . || true)
if [ "$n" != 1 ]; then
  echo "FAIL: expected exactly one line mentioning sorry (the challenge's warning), found $n:"
  printf '%s\n' "$hits" | sed 's/^/  /'
  exit 1
fi
if ! printf '%s\n' "$hits" | grep -qxE "warning: (\./)*CN1Challenges/ClassNumberOne\.lean:[0-9]+:[0-9]+: declaration uses .sorry."; then
  echo "FAIL: the one sorry line is not the challenge statement's warning:"
  printf '  %s\n' "$hits"
  exit 1
fi
echo "OK: the only sorry is the challenge statement's: $hits"
