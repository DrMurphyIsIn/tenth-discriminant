#!/usr/bin/env bash
# Regenerate the frozen, generated inputs of the Lean proof from the generators in this directory
# and compare them byte for byte with what is checked in. Exit 0 iff everything agrees.
#
#   witnesses.py            -> witnesses.json           (the split-prime witness per fundamental -d)
#   gen_witnesses.py        -> formalization/CN1/Finite/Witnesses.lean, Witnesses/Chunk1..4.lean
#   gen_zeta_tables.py      -> formalization/CN1/Numerics/ZetaTables.lean
#   gen_gamma_numbers.py    -> the integer brackets quoted in formalization/CN1/Numerics/GammaRatio.lean
#   gen_threshold_numbers.py-> the integer brackets quoted in formalization/CN1/Numerics/Threshold.lean
#
# The generators are pure Python 3 (exact integer and rational arithmetic, no floats in anything
# that reaches Lean). Nothing here is part of the proof: the Lean kernel re-checks every emitted
# fact when the project is built. This script only shows that the checked-in data is what the
# generators produce. Run from anywhere; everything is written to certificates/_regen/, which is
# removed on success and kept for inspection on failure.
set -uo pipefail
cd "$(dirname "$0")"
FORM=../formalization/CN1
R=_regen
rm -rf "$R"; mkdir -p "$R/Finite" "$R/Numerics"
fail=0
ok()  { printf 'ok    %s\n' "$*"; }
bad() { printf 'FAIL  %s\n' "$*"; fail=1; }

# --- witnesses.json -----------------------------------------------------------------------------
OMP_NUM_THREADS=1 python3 witnesses.py "$R/witnesses.json" > "$R/witnesses.summary.txt" || bad "witnesses.py exited non-zero"
# The summary carries a run label; the rows (the data gen_witnesses.py reads) must agree exactly.
python3 - "$R/witnesses.json" witnesses.json <<'EOF' || bad "witnesses.json rows differ from the regenerated data"
import json, sys
a, b = (json.load(open(p)) for p in sys.argv[1:3])
sa = {k: v for k, v in a["summary"].items() if k != "label"}
sb = {k: v for k, v in b["summary"].items() if k != "label"}
sys.exit(0 if (a["rows"] == b["rows"] and sa == sb) else 1)
EOF
[ $fail = 0 ] && ok "witnesses.json: 197 rows and summary (apart from the run label) reproduced"

# --- the generated Lean files -------------------------------------------------------------------
python3 gen_witnesses.py "$R/Finite" > "$R/gen_witnesses.out" || bad "gen_witnesses.py exited non-zero"
for f in Witnesses.lean Witnesses/Chunk1.lean Witnesses/Chunk2.lean Witnesses/Chunk3.lean Witnesses/Chunk4.lean; do
  if cmp -s "$R/Finite/$f" "$FORM/Finite/$f"; then ok "CN1/Finite/$f byte-identical"; else bad "CN1/Finite/$f differs"; fi
done
python3 gen_zeta_tables.py "$R/Numerics/ZetaTables.lean" > "$R/gen_zeta_tables.out" || bad "gen_zeta_tables.py exited non-zero"
if cmp -s "$R/Numerics/ZetaTables.lean" "$FORM/Numerics/ZetaTables.lean"; then ok "CN1/Numerics/ZetaTables.lean byte-identical"; else bad "CN1/Numerics/ZetaTables.lean differs"; fi

# --- numbers quoted in hand-written Lean files ----------------------------------------------------
# Both directions: every bracket a generator prints for a quantity the Lean file uses appears in the
# file, and every bracket constant the Lean file quotes is one the generator printed.
sfail=0
# gen_zeta_tables.py also prints the single brackets (lo, hi at scale 10^12) for N = 1001; ZetaValues.lean
# quotes them as `(<n> : ℝ) / 1000000000000` (only the sides its lemmas need).
gen=$(grep -o 'lo=[0-9]* hi=[0-9]*' "$R/gen_zeta_tables.out" | grep -o '[0-9]*' | sort -u)
used=$(grep -o '([0-9]* : ℝ) / 1000000000000' "$FORM/Numerics/ZetaValues.lean" | grep -o '[0-9]*' | grep -v '^1000000000000$' | sort -u)
for n in $used; do echo "$gen" | grep -qx "$n" || { bad "ZetaValues.lean quotes $n, which gen_zeta_tables.py does not print"; sfail=1; }; done
for n in $(grep -o 'hi=[0-9]*' "$R/gen_zeta_tables.out" | grep -o '[0-9]*'); do echo "$used" | grep -qx "$n" || { bad "ZetaValues.lean lacks the upper bracket $n"; sfail=1; }; done
[ $sfail = 0 ] && ok "ZetaValues.lean: all $(echo "$used" | wc -l | tr -d ' ') quoted N = 1001 brackets are gen_zeta_tables.py output, every upper bracket is used"
sfail=0
python3 gen_gamma_numbers.py > "$R/gen_gamma_numbers.out" 2>/dev/null || { bad "gen_gamma_numbers.py exited non-zero"; sfail=1; }
gen=$(grep -E '^(l1|u2|u3|l4) =' "$R/gen_gamma_numbers.out" | grep -o '[0-9]\{6,\}' | sort -u)
used=$(grep -o '([0-9]\{6,\} : ℝ) / 1000000000000' "$FORM/Numerics/GammaRatio.lean" | grep -o '[0-9]\{6,\}' | grep -v '^1000000000000$' | sort -u)
for n in $gen; do echo "$used" | grep -qx "$n" || { bad "GammaRatio.lean lacks the bracket $n"; sfail=1; }; done
for n in $used; do echo "$gen" | grep -qx "$n" || { bad "GammaRatio.lean quotes $n, which gen_gamma_numbers.py does not print"; sfail=1; }; done
grep -q '^key1: True' "$R/gen_gamma_numbers.out" && grep -q '^key2: True' "$R/gen_gamma_numbers.out" || { bad "gen_gamma_numbers.py: a key inequality is False"; sfail=1; }
[ $sfail = 0 ] && ok "GammaRatio.lean: l1, u2, u3, l4 agree with gen_gamma_numbers.py in both directions; both key inequalities hold"
sfail=0
python3 gen_threshold_numbers.py > "$R/gen_threshold_numbers.out" || { bad "gen_threshold_numbers.py exited non-zero"; sfail=1; }
gen=$(grep -E '^(2\^\(3/4\)|655\^\(-3/8\)|sqrt\(pi\)) in' "$R/gen_threshold_numbers.out" | grep -o '[0-9]\{7,\}' | sort -u)
used=$(grep -o '([0-9]\{7,\} : ℝ) / 10\{7,8\}\b' "$FORM/Numerics/Threshold.lean" | grep -o '^([0-9]*' | tr -d '(' | sort -u)
for n in $gen; do echo "$used" | grep -qx "$n" || { bad "Threshold.lean lacks the bracket $n"; sfail=1; }; done
for n in $used; do echo "$gen" | grep -qx "$n" || { bad "Threshold.lean quotes $n, which gen_threshold_numbers.py does not print"; sfail=1; }; done
grep -q 'M_lo - B0_hi = .* > 0: True' "$R/gen_threshold_numbers.out" || { bad "gen_threshold_numbers.py: M(655) - B0(655) > 0 not confirmed"; sfail=1; }
[ $sfail = 0 ] && ok "Threshold.lean: the 2^(3/4), 655^(-3/8), sqrt(pi) brackets agree with gen_threshold_numbers.py in both directions"

if [ $fail = 0 ]; then rm -rf "$R"; echo "ALL OK"; else echo "FAILED (outputs kept in $R)"; exit 1; fi
