"""Bernstein-basis interval positivity, compile-gated.

Proves `0 <= p(x)` on a closed interval `[a, b]` from nonnegative Bernstein
coefficients (Telperion FINDS them, elevating the degree). The univariate,
interval specialization of Handelman positivity.

Demonstrations: 0 <= 1 - x^2 on [-1,1] (= (1+x)(1-x)); 0 <= 2 - x on [0,1];
0 <= x^2 - x + 1 on [0,1] (strictly positive, needs elevation).
NEGATIVE CONTROL: x on [-1,1] takes negative values -> refused.
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (BernsteinEmitter, CertificationError, GridSpec, LeanProfile,
    ValidationReport, bernstein_family, certify, diff_frozen, emit, freeze)
HERE = Path(__file__).resolve().parent
x = sp.symbols("x")
CASES = {
    0: ("bernstein_1_minus_x2", 1 - x**2, -1, 1),
    1: ("bernstein_2_minus_x", 2 - x, 0, 1),
    2: ("bernstein_x2_minus_x_plus_1", x**2 - x + 1, 0, 1),
}
def _family():
    return bernstein_family("Bernstein", (x,), GridSpec([("i", [0, 1, 2])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2], CASES[pt["i"]][3]))
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "Bernstein")),
        [BernsteinEmitter()], _validation(), file_name="Bernstein.lean")
def _validation():
    def d():
        bad = bernstein_family("Bad", (x,), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: (x, -1, 1))
        try: certify(bad); raise AssertionError("sign-indefinite not refused")
        except CertificationError: pass
    return ValidationReport.from_asserts([("bernstein_discriminates", d)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"Bernstein: {res.n_theorems} interval certs, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
