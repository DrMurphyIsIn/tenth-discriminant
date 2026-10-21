"""Finite-decide certificates over explicit tables, compile-gated.

Crystallized from gen_petersen_cert.py (2026-08-20): guarded decidable
universally-quantified facts over Nat-bitmask/sign tables, proven by kernel
`decide` (arithmetic in ℕ/ℤ only — ℚ does not kernel-reduce).

Demonstration: a consistent single-clause 3XOR closure on 6 variables — the
pairFact shape (sign multiplicativity across index-compatible closure pairs)
for lam = {∅:+1, {2,3,4}:+1} and the 22 degree-<=2 index masks.
NEGATIVE CONTROL: an inconsistent sign table (sgn(3^^^5) = -1 against
sgn(3)*sgn(5) = +1) is refused at exact evaluation.
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, itertools, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (CertificationError, Cmp, FiniteDecideEmitter, ForallIn,
    GridSpec, Imp, LeanProfile, Lit, Lookup, Mul, NatTable, PairTable, Pop,
    ValidationReport, Var, Xor, certify, diff_frozen, emit, finite_decide_family, freeze)
HERE = Path(__file__).resolve().parent

def idx_masks(nbits, d):
    out = []
    for k in range(d + 1):
        for c in itertools.combinations(range(nbits), k):
            out.append(sum(1 << i for i in c))
    return sorted(out)

def pair_prop():
    tables = [PairTable("lam", [(0, 1), (0b11100, 1)]),
              NatTable("lamKeys", [0, 0b11100]),
              NatTable("idx", idx_masks(6, 2))]
    sgn = lambda e: Lookup("lam", e)
    prop = ForallIn("a", "lamKeys",
             ForallIn("b", "lamKeys",
               ForallIn("t", "idx",
                 Imp(Cmp("le", Pop(Xor(Var("a"), Var("t"))), Lit(2)),
                   Imp(Cmp("le", Pop(Xor(Var("b"), Var("t"))), Lit(2)),
                     Cmp("eq", sgn(Xor(Var("a"), Var("b"))),
                         Mul(sgn(Var("a")), sgn(Var("b")))))))))
    return tables, prop

def _family():
    return finite_decide_family("FiniteDecide", GridSpec([("i", [0])]),
        lambda pt: "finite_decide_xor3_pairfact", lambda pt: pair_prop())
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "FiniteDecide")),
        [FiniteDecideEmitter()], _validation(), file_name="FiniteDecide.lean")
def _validation():
    def inconsistent_refused():
        def bad_spec(pt):
            tables = [PairTable("lam", [(0, 1), (3, 1), (5, 1), (6, -1)]),
                      NatTable("lamKeys", [0, 3, 5, 6]),
                      NatTable("idx", idx_masks(4, 2))]
            sgn = lambda e: Lookup("lam", e)
            prop = ForallIn("a", "lamKeys", ForallIn("b", "lamKeys",
                ForallIn("t", "idx",
                  Imp(Cmp("le", Pop(Xor(Var("a"), Var("t"))), Lit(2)),
                    Imp(Cmp("le", Pop(Xor(Var("b"), Var("t"))), Lit(2)),
                      Cmp("eq", sgn(Xor(Var("a"), Var("b"))),
                          Mul(sgn(Var("a")), sgn(Var("b")))))))))
            return tables, prop
        bad = finite_decide_family("Bad", GridSpec([("i", [0])]),
            lambda pt: "bad", bad_spec)
        try: certify(bad); raise AssertionError("inconsistent table not refused")
        except CertificationError: pass
    return ValidationReport.from_asserts([
        ("finite_decide_discriminates", inconsistent_refused)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"FiniteDecide: {res.n_theorems} certs, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
