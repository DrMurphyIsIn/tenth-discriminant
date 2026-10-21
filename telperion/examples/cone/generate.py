"""Cone/Farkas nonnegative-combination certificates, compile-gated.

Proves `0 ≤ target` by writing `target = Σ λᵢ·bᵢ` with every `λᵢ ≥ 0` and every
basis element `bᵢ` `positivity`-provable — a nonnegative combination over a
supplied basis.  Telperion FINDS the weights exactly (rational linear solve;
an OVERCOMPLETE basis falls through to basic-feasible-solution enumeration —
the sympy-only vertex search that closes the former "needs LP" gap).

Demonstrations (every basis element `positivity`-provable — squares):
  * determined: `(x+y)²` via the single basis element `(x+y)²`;
  * OVERCOMPLETE (BFS): `(x+y)²` via `{x², y², (x−y)², (x+y)²}` (4 elements, 3
    monomial equations — underdetermined; a vertex certificate is enumerated);
  * OVERCOMPLETE multi-term: `x² + y²` via `{x², y², (x−y)², (x+y)²}`
    (the vertex `x² + y²`; zero-weight elements are dropped from the emission).

NEGATIVE CONTROL (in validation): `−x²` is not a nonnegative combination of
`{x², y², (x+y)²}` — refused with a Farkas dual.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    CertificationError, ConeFarkasEmitter, GridSpec, LeanProfile,
    ValidationReport, certify, cone_family, diff_frozen, emit, freeze,
)

HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")

# pt index -> (lean_name, target, basis)
CASES = {
    0: ("cone_square_direct", (x + y) ** 2, [(x + y) ** 2]),
    1: ("cone_square_overcomplete", (x + y) ** 2,
        [x ** 2, y ** 2, (x - y) ** 2, (x + y) ** 2]),
    2: ("cone_sum_of_squares", x ** 2 + y ** 2,
        [x ** 2, y ** 2, (x - y) ** 2, (x + y) ** 2]),
}


def _family():
    return cone_family(
        "Cone", (x, y), GridSpec([("i", [0, 1, 2])]),
        lambda pt: CASES[pt["i"]][0],
        lambda pt: (CASES[pt["i"]][1], CASES[pt["i"]][2]))


def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "Cone")),
                [ConeFarkasEmitter()], _validation(), file_name="Cone.lean")


def _validation() -> ValidationReport:
    def infeasible_refused():
        bad = cone_family(
            "Bad", (x, y), GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: (-x ** 2, [x ** 2, y ** 2, (x + y) ** 2]))
        try:
            certify(bad)
            raise AssertionError("infeasible cone target was NOT refused")
        except CertificationError:
            pass

    return ValidationReport.from_asserts(
        [("cone_infeasible_refused", infeasible_refused)])


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
    print(f"Cone: {res.n_theorems} nonnegative-combination certificates, "
          f"hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
