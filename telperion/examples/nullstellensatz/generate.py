"""Nullstellensatz / ideal-membership certificates, compile-gated.

Proves that a polynomial VANISHES on an algebraic variety — an EQUALITY, not an
inequality — from ideal-membership cofactors `p = Σ h_i·g_i` (computed by Gröbner
reduction).  If `p` lies in `⟨g_1, …, g_m⟩`, then `p = 0` wherever all generators
vanish.

Demonstrations:
  * `x³ − y³ = 0` on `V(x − y)`, cofactor `x² + xy + y²`;
  * `x·y = 0` on `V(x, y)` (two generators).

NEGATIVE CONTROL (in validation): `x² + 1`, which is not in `⟨x − y⟩`, is refused
(nonzero remainder).

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, LeanProfile, NullstellensatzEmitter,
    ValidationReport, certify, diff_frozen, emit, freeze, nullstellensatz_family,
)

HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")

# pt index -> (lean_name, p, generators)
CASES = {
    0: ("nss_x3_minus_y3", x ** 3 - y ** 3, [x - y]),
    1: ("nss_xy_in_xy", x * y, [x, y]),
}


def _family():
    return nullstellensatz_family(
        "Nullstellensatz", (x, y), GridSpec([("i", [0, 1])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2]))


def build():
    return emit(certify(_family()),
                LeanProfile(namespace=("G1", "Nullstellensatz")),
                [NullstellensatzEmitter()], _validation(),
                file_name="Nullstellensatz.lean")


def _validation() -> ValidationReport:
    def discriminates():
        bad = nullstellensatz_family(
            "Bad", (x, y), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: (x ** 2 + 1, [x - y]))  # not in the ideal
        try:
            certify(bad)
            raise AssertionError("non-member was NOT refused")
        except CertificationError:
            pass
    return ValidationReport.from_asserts([("nss_discriminates", discriminates)])


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    res = build()
    if args.check:
        rep = diff_frozen(res, HERE / "frozen")
        print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok:
            print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen")
    print(f"Nullstellensatz: {res.n_theorems} ideal-membership certificates, "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
