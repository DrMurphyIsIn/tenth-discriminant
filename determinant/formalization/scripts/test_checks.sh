#!/usr/bin/env bash
# test_checks.sh: self-test of check_axioms.sh and check_no_sorry.sh.
#
# Runs each check over every fixture in scripts/fixtures/<check>/accept/ (each must pass, exit 0) and
# scripts/fixtures/<check>/reject/ (each must fail, exit non-zero), and over a missing file (must fail). Prints one line per
# case and exits 0 exactly when every case behaves as expected. The workflow runs it before the real checks, so a check
# that has stopped rejecting what it should cannot pass silently.
#
# Fixtures whose names begin with real_ are captured output: from the CI run, from the fresh build recorded in
# VERIFICATION.md, from the run of record, or from small core-Lean files that print an axiom list (for example an axiom
# named «#evil[», which Lean prints unescaped). The others are constructed.
set -uo pipefail
cd "$(dirname "$0")"
bad=0
total=0
run() {  # run <check script> <fixture> <expected: accept|reject>
  local script=$1 fx=$2 want=$3 got
  if ./"$script" "$fx" > /dev/null 2>&1; then got=accept; else got=reject; fi
  total=$((total + 1))
  if [ "$got" = "$want" ]; then
    printf 'ok    %-16s %-7s %s\n' "$script" "$want" "${fx#fixtures/}"
  else
    printf 'WRONG %-16s %-7s %s (got %s)\n' "$script" "$want" "${fx#fixtures/}" "$got"
    bad=$((bad + 1))
  fi
}
for pair in check_axioms.sh:axioms check_no_sorry.sh:sorry; do
  script=${pair%%:*}; dir=fixtures/${pair#*:}
  for want in accept reject; do
    n=0
    for fx in "$dir/$want"/*; do
      [ -f "$fx" ] || continue
      run "$script" "$fx" "$want"; n=$((n + 1))
    done
    [ "$n" -gt 0 ] || { echo "WRONG no fixtures in $dir/$want"; bad=$((bad + 1)); }
  done
  run "$script" "$dir/does-not-exist" reject
done
if [ "$bad" = 0 ]; then echo "ALL $total CASES OK"; else echo "$bad OF $total CASES WRONG"; exit 1; fi
