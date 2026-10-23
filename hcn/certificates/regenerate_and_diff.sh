#!/usr/bin/env bash
# Regenerate every generated Lean file of the HCN proof from the generators in this directory and compare them byte
# for byte with what is checked in. Exit 0 iff everything agrees.
#
#   gen_sets.py     -> formalization/HCNChallenges/ClassNumberLeTwo.lean   (the two radicand sets of the statement)
#   gen_certs.py    -> formalization/HCN/Finite/Certs.lean, Certs/Chunk1.lean ... Chunk15.lean   (1,429 certificates)
#   gen_classtwo.py -> formalization/HCN/Finite/ClassTwo.lean               (the 18 fields of class number two)
#   gen_range.py    -> formalization/HCN/Assembly/Range.lean, HCN/Assembly.lean, HCN/Main.lean (from Main.lean.in)
#   gen_controls.py -> formalization/HCNNegControls/Tamper/*.lean           (the three tampered statements)
#
# The generators are pure Python 3 (exact integer arithmetic; standard library only) and read the computed class-number
# data in data/. Nothing here is part of the proof: the Lean kernel re-checks every certificate when the project is
# built, and the statement's sets are checked by reading them. This script only shows that the checked-in files are
# what the generators produce. Run from anywhere; everything is written to certificates/_regen/, which is removed on
# success and kept for inspection on failure. It takes about ten seconds.
set -uo pipefail
cd "$(dirname "$0")"
F=../formalization
R=_regen
rm -rf "$R"; mkdir -p "$R"
fail=0
ok()  { printf 'ok    %s\n' "$*"; }
bad() { printf 'FAIL  %s\n' "$*"; fail=1; }
run() { local name=$1; shift; if "$@" > "$R/$name.out" 2>&1; then ok "$name: $(tail -1 "$R/$name.out")"; else bad "$name exited non-zero (see $R/$name.out)"; fi; }

# the order matters: each step reads what the previous ones wrote under _regen/
if python3 gen_sets.py "$R" > "$R/gen_sets_out.txt" 2>&1 && grep -q '^h = 1 radicands (9)' "$R/gen_sets_out.txt" && grep -q '^h = 2 radicands (18)' "$R/gen_sets_out.txt"; then
  ok "gen_sets.py: 9 radicands with h = 1 and 18 with h = 2; all five class-number sources agree"
else bad "gen_sets.py exited non-zero or found other sets (see $R/gen_sets_out.txt)"; fi
run gen_certs python3 gen_certs.py "$R"
run gen_classtwo python3 gen_classtwo.py "$R"
run gen_range python3 gen_range.py "$R"
run gen_controls python3 gen_controls.py "$R"

n=0
for f in HCNChallenges/ClassNumberLeTwo.lean HCN/Finite/Certs.lean HCN/Finite/ClassTwo.lean HCN/Assembly/Range.lean \
         HCN/Assembly.lean HCN/Main.lean HCNNegControls/Tamper/Move163.lean HCNNegControls/Tamper/DropSquarefree.lean \
         HCNNegControls/Tamper/Swap431.lean $(cd "$F" && ls HCN/Finite/Certs/Chunk*.lean); do
  n=$((n + 1))
  if cmp -s "$R/$f" "$F/$f"; then ok "$f byte-identical"; else bad "$f differs"; fi
done
# no generated file may be missing from the checked-in tree, and no checked-in chunk may be extra
for f in $(cd "$R" && ls HCN/Finite/Certs/Chunk*.lean); do [ -f "$F/$f" ] || bad "$f generated but not checked in"; done

# the negative controls of the generators: written outside the Lean library, each must fail to build (see README.md)
python3 gen_certs.py --force-controls "$R/controls" > "$R/controls_certs.out" 2>&1 && \
python3 gen_classtwo.py --force-controls "$R/controls" > "$R/controls_classtwo.out" 2>&1 && \
  ok "generator controls written: $(ls "$R/controls" | tr '\n' ' ')" || bad "a --force-controls run failed"

if [ $fail = 0 ]; then rm -rf "$R"; echo "ALL OK ($n generated files)"; else echo "FAILED (outputs kept in $R)"; exit 1; fi
