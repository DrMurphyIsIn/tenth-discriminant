#!/usr/bin/env bash
# check_axioms.sh <file>: check the output of `#print axioms CN1.classNumber_eq_one_iff`.
#
# Passes (exit 0) exactly when the file contains one closed list
#   'CN1.classNumber_eq_one_iff' depends on axioms: [...]
# whose entries are all among propext, Classical.choice and Quot.sound, and the file does not
# mention sorryAx anywhere. Lean prints a long axiom list one entry per line, so the file is joined
# into one line first; a line-based check would miss an entry on a continuation line.
#
# The output must come from a file whose only project import is ELEM.Main: importing ELEM.Main
# together with CN1Challenges.ClassNumberOne or a control makes `#print axioms` unreliable
# (README.md, "One rule").
set -uo pipefail
f=${1:?usage: check_axioms.sh <print-axioms output>}
joined=$(tr '\n' ' ' < "$f")
if printf '%s' "$joined" | grep -q 'sorryAx'; then
  echo "FAIL: sorryAx in the axiom output"; exit 1
fi
lists=$(printf '%s' "$joined" | grep -oE "'CN1\.classNumber_eq_one_iff' depends on axioms: \[[^]]*\]" || true)
n=$(printf '%s' "$lists" | grep -c 'depends on axioms' || true)
if [ "$n" != 1 ]; then
  echo "FAIL: expected one closed axiom list for CN1.classNumber_eq_one_iff, found $n"; exit 1
fi
axioms=$(printf '%s' "$lists" | sed -E 's/.*\[(.*)\]/\1/' | tr ',' '\n' | tr -d ' \t' | grep -v '^$' || true)
if [ -z "$axioms" ]; then
  echo "FAIL: empty axiom list"; exit 1
fi
extra=$(printf '%s\n' "$axioms" | grep -vxF -e propext -e Classical.choice -e Quot.sound || true)
if [ -n "$extra" ]; then
  echo "FAIL: axioms outside propext, Classical.choice, Quot.sound:"; printf '  %s\n' $extra; exit 1
fi
echo "OK: CN1.classNumber_eq_one_iff depends only on: $(printf '%s ' $axioms)"
