#!/usr/bin/env bash
# Regenerate the eight residue-sieve chunk files of the determinant proof from gen_sieve.py and
# compare them byte for byte with what is checked in. Exit 0 iff everything agrees.
#
#   gen_sieve.py -> determinant/formalization/ELEM/Sieve/Chunk0.lean ... Chunk7.lean
#                   (and two negative controls, which are not checked in; see README.md)
#
# The generator is pure Python 3 (standard library, exact integer arithmetic). Nothing here is part
# of the proof: the Lean kernel re-checks every chunk with `decide +kernel` when the project is built.
# This script only shows that the checked-in chunks are what the generator produces, and that the
# generator's own counts (4,095 candidates, the five survivors, and where each control must fail)
# come out as recorded. Run from anywhere; everything is written to certificates/_regen/, which is
# removed on success and kept for inspection on failure.
set -uo pipefail
cd "$(dirname "$0")"
SIEVE=../formalization/ELEM/Sieve
R=_regen
rm -rf "$R"; mkdir -p "$R"
fail=0
ok()  { printf 'ok    %s\n' "$*"; }
bad() { printf 'FAIL  %s\n' "$*"; fail=1; }

if python3 gen_sieve.py "$R" > "$R/gen_sieve.out"; then
  ok "gen_sieve.py: $(grep -c '^chunk ' "$R/gen_sieve.out") chunks, survivors $(grep '^survivors:' "$R/gen_sieve.out" | cut -d: -f2 | tr -d ' '), CHECKS PASS"
else
  bad "gen_sieve.py exited non-zero (its counts disagree with the record; see $R/gen_sieve.out)"
fi
for i in 0 1 2 3 4 5 6 7; do
  f=Chunk$i.lean
  if cmp -s "$R/ELEM/Sieve/$f" "$SIEVE/$f"; then ok "ELEM/Sieve/$f byte-identical"; else bad "ELEM/Sieve/$f differs"; fi
done
# The two controls are the real chunk statement with one list changed. They are generated here, not
# checked in, and they must fail to compile (see README.md).
for c in Control_No31_Chunk7:7:sievePrimesNo31 Control_167_Chunk0:0:survivors167; do
  name=${c%%:*}; rest=${c#*:}; i=${rest%%:*}; list=${rest#*:}
  if [ -f "$R/controls/$name.lean" ] && grep -q "$list" "$R/controls/$name.lean"; then
    ok "controls/$name.lean generated (uses $list; must FAIL to compile, see README.md)"
  else
    bad "controls/$name.lean missing or does not use $list"
  fi
done

if [ $fail = 0 ]; then rm -rf "$R"; echo "ALL OK"; else echo "FAILED (outputs kept in $R)"; exit 1; fi
