#!/usr/bin/env bash
# check_no_sorry.sh <build log>: check the log of `lake build HCN CN1 HCNChallenges`.
#
# Passes exactly when the log reports a successful build and contains exactly two lines that mention `sorry`, and they
# are the warnings for the two challenge statements, at two different positions:
#   warning: HCNChallenges/ClassNumberLeTwo.lean:<line>:<col>: declaration uses `sorry`
# (the challenge is a `sorry` by design, as Comparator requires). It fails closed: on a missing or empty log, a log
# without "Build completed successfully", a log without both challenge warnings, any further sorry warning (including a
# third one in HCNChallenges/), any other line that mentions sorry, and any mention of sorryAx.
# scripts/test_checks.sh runs this script over the fixtures in scripts/fixtures/.
set -uo pipefail
f=${1:?usage: check_no_sorry.sh <lake build log>}
[ -s "$f" ] || { echo "FAIL: missing or empty build log: $f"; exit 1; }
grep -q 'Build completed successfully' "$f" || { echo "FAIL: the log does not report a successful build"; exit 1; }
if grep -q 'sorryAx' "$f"; then
  echo "FAIL: sorryAx in the build log"; exit 1
fi
hits=$(grep -i 'sorry' "$f" || true)
n=$(printf '%s' "$hits" | grep -c . || true)
if [ "$n" != 2 ]; then
  echo "FAIL: expected exactly two lines mentioning sorry (the two challenge statements), found $n:"
  printf '%s\n' "$hits" | sed 's/^/  /'
  exit 1
fi
# A leading ./ is dropped before the positions are compared, so one warning printed twice, once as ./HCNChallenges/..., is
# counted once.
good=$(printf '%s\n' "$hits" | grep -xE "warning: (\./)*HCNChallenges/ClassNumberLeTwo\.lean:[0-9]+:[0-9]+: declaration uses .sorry." \
  | sed -E 's#^warning: (\./)*#warning: #' | sort -u | grep -c . || true)
if [ "$good" != 2 ]; then
  echo "FAIL: the two sorry lines are not the warnings of the two challenge statements at two positions:"
  printf '%s\n' "$hits" | sed 's/^/  /'
  exit 1
fi
echo "OK: the only sorries are the two challenge statements':"; printf '%s\n' "$hits" | sed 's/^/  /'
