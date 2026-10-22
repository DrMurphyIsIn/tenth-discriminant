#!/usr/bin/env bash
# check_axioms.sh <file>: check the output of `lake env lean AxiomCheck.lean`, where AxiomCheck.lean imports only ELEM.Main
# and runs `#print axioms CN1.classNumber_eq_one_iff`.
#
# Passes exactly when the WHOLE file, with all whitespace removed (so however Lean wraps the list), is one `#print axioms`
# report for CN1.classNumber_eq_one_iff whose entries are all among propext, Classical.choice and Quot.sound. Nothing else
# may appear except an optional `info: <file>:<line>:<col>:` prefix: no error line, no second report, no other text. Lean
# prints some names unescaped (a root starting with '#' or '?', an inaccessible or macro-scoped name), and such a name may
# contain '[' or ']'; matching the whole output means it can never move the list boundaries. An earlier version of this
# script extracted the list after the last '[' and could be fooled that way. A missing or empty file fails.
#
# The output must come from a file whose only project import is ELEM.Main: importing ELEM.Main together with
# CN1Challenges.ClassNumberOne or a control makes `#print axioms` unreliable (README.md, "One rule").
# scripts/test_checks.sh runs this script over the fixtures in scripts/fixtures/.
set -uo pipefail
f=${1:?usage: check_axioms.sh <output of lake env lean AxiomCheck.lean>}
[ -s "$f" ] || { echo "FAIL: missing or empty output: $f"; exit 1; }
norm=$(tr -d ' \t\r\n' < "$f")
std='(propext|Classical\.choice|Quot\.sound)'
if printf '%s\n' "$norm" | grep -qxE "(info:[^']*:[0-9]+:[0-9]+:)?'CN1\.classNumber_eq_one_iff'dependsonaxioms:\[${std}(,${std})*\]"; then
  echo "OK: CN1.classNumber_eq_one_iff depends only on standard axioms: ${norm#*\[}" | sed 's/\]$//'
  exit 0
fi
echo "FAIL: the output is not exactly one axiom list for CN1.classNumber_eq_one_iff over propext, Classical.choice and Quot.sound:"
sed 's/^/  /' "$f"
exit 1
