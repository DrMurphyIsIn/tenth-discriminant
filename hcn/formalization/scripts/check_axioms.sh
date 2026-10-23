#!/usr/bin/env bash
# check_axioms.sh <file>: check the output of `lake env lean AxiomCheck.lean`, where AxiomCheck.lean imports only HCN.Main
# and runs `#print axioms HCN.classNumber_le_two_iff` and then `#print axioms HCN.classNumber_eq_two_iff`.
#
# Passes exactly when the WHOLE file, with all whitespace removed (so however Lean wraps the lists), is those two
# `#print axioms` reports, in that order, and every entry of each list is one of propext, Classical.choice and
# Quot.sound. Nothing else may appear except an optional `info: <file>:<line>:<col>:` prefix before each report, whose
# <file> may contain neither a quote nor a colon, so that the prefix cannot swallow an `error:` line: no error
# line, no further report, no other text. Lean prints some names unescaped (a root starting with '#' or '?', an
# inaccessible or macro-scoped name), and such a name may contain '[' or ']'; matching the whole output means it can
# never move the list boundaries. A missing or empty file fails. This is the determinant route's check
# (../../../determinant/formalization/scripts/check_axioms.sh) for two theorems instead of one, with that tighter prefix.
#
# The output must come from a file whose only project import is HCN.Main: importing HCN.Main together with
# HCNChallenges.ClassNumberLeTwo or a control makes `#print axioms` unreliable (README.md, "One rule").
# scripts/test_checks.sh runs this script over the fixtures in scripts/fixtures/.
set -uo pipefail
f=${1:?usage: check_axioms.sh <output of lake env lean AxiomCheck.lean>}
[ -s "$f" ] || { echo "FAIL: missing or empty output: $f"; exit 1; }
norm=$(tr -d ' \t\r\n' < "$f")
std='(propext|Classical\.choice|Quot\.sound)'
list="\[${std}(,${std})*\]"
pre="(info:[^':]*:[0-9]+:[0-9]+:)?"
if printf '%s\n' "$norm" | grep -qxE "${pre}'HCN\.classNumber_le_two_iff'dependsonaxioms:${list}${pre}'HCN\.classNumber_eq_two_iff'dependsonaxioms:${list}"; then
  echo "OK: HCN.classNumber_le_two_iff and HCN.classNumber_eq_two_iff depend only on standard axioms"
  exit 0
fi
echo "FAIL: the output is not exactly the two axiom lists, for HCN.classNumber_le_two_iff and HCN.classNumber_eq_two_iff,"
echo "      over propext, Classical.choice and Quot.sound:"
sed 's/^/  /' "$f"
exit 1
