"""Infeasibility / Nullstellensatz-refutation certificates, compile-gated.

Proves a polynomial system `{g_j = 0}` has NO common solution — a certificate of
NON-existence (the dual of vanishing-on-a-variety) — from a refutation
`1 = Σ λ_j g_j` that Telperion computes by undetermined coefficients.

Demonstrations:
  * `{x = 0, x − 1 = 0}` — inconsistent, refuted by `1 = 1·x + (−1)·(x−1)`;
  * `{x² − 1 = 0, x − 2 = 0}` — no common root, refuted with rational cofactors.

NEGATIVE CONTROL (in validation): the satisfiable `{x − y = 0}` yields no
refutation and is refused.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CertificationError, GridSpec, InfeasibilityEmitter, LeanProfile,
    ValidationReport, certify, diff_frozen, emit, freeze, infeasible_family,
)

HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")

CASES = {
    0: ("infeasible_x_and_x_minus_1", [x, x - 1]),
    1: ("infeasible_x2m1_and_x_minus_2", [x ** 2 - 1, x - 2]),
}


def _family():
    return infeasible_family(
        "Infeasible", (x, y), GridSpec([("i", [0, 1])]),
        lambda pt: CASES[pt["i"]][0], lambda pt: CASES[pt["i"]][1])


def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "Infeasible")),
                [InfeasibilityEmitter()], _validation(),
                file_name="Infeasible.lean")


def _validation() -> ValidationReport:
    def discriminates():
        bad = infeasible_family(
            "Bad", (x, y), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: [x - y])  # satisfiable -> no refutation
        try:
            certify(bad)
            raise AssertionError("satisfiable system was NOT refused")
        except CertificationError:
            pass
    return ValidationReport.from_asserts([("infeasible_discriminates", discriminates)])


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
    print(f"Infeasible: {res.n_theorems} refutation certificates, "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
