"""SDP-SOS certificates with complementary-slackness duality, compile-gated.

The LP -> SDP upgrade: certify p >= 0 by a PSD Gram matrix (off-diagonal
coupling), reaching polynomials that vanish at INTERIOR points -- the tie shapes
Polya lifting cannot handle -- and reading the equality variety off the dual
(the square bases' common zeros) FOR FREE.

As of 2026-08-18 this flows through the FIRST-CLASS SOS pipeline: `sos_family`
+ `SOSEmitter` under the enforced certify() -> emit() -> freeze() API, with the
declared interior ties cross-checked against the SDP dual's tight variety (an
over-claiming certificate is refused).  The family is the parametric
interior-tie pencil p_a = (x-a)^2 + (y-1)^2 + (x-y-(a-1))^2, whose a=1 member is
the original single demonstrator (interior tight zero at (1,1)); a=2,3 move the
interior tie, exercising the off-diagonal Gram coupling per instance.

HONEST SCOPE: this is the certificate LAYER the occupancy / "SOS for limits of
trees" method runs on.  Aiming it at the recursive matching-functional profile
so the dual lands on the integer tie s=5 is the named research program (unbounded
degree + arithmetic tie), NOT delivered here.  conjecture1_proved=False.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    LeanProfile,
    SOSEmitter,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
    sos_family,
)
from telperion.sos_sdp import sos_sdp_certificate  # noqa: E402

HERE = Path(__file__).resolve().parent
x, y = sp.symbols("x y")

A_VALUES = [1, 2, 3]


def _p(a: int) -> sp.Expr:
    """Interior-tie pencil; tight zero at (a, 1).  a=1 is the original
    demonstrator 2x^2 - 2xy + 2y^2 - 2x - 2y + 2."""
    return sp.expand((x - a) ** 2 + (y - 1) ** 2 + (x - y - (a - 1)) ** 2)


def _lean_name(pt) -> str:
    a = pt["a"]
    # a=1 keeps the original theorem name for continuity (imported by proof_audit).
    return "sdp_sos_interior_tie" if a == 1 else f"sdp_sos_interior_tie_a{a}"


def build():
    fam = sos_family(
        name="SOSSDP",
        symbols=(x, y),
        grid=GridSpec([("a", A_VALUES)]),
        lean_name=_lean_name,
        target=lambda pt: _p(pt["a"]),
        half_deg=1,
        ties=lambda pt: [{x: pt["a"], y: 1}],
    )
    return emit(certify(fam), LeanProfile(namespace=("G1", "SOSSDP")),
                [SOSEmitter()], _validation(), file_name="SOSSDP.lean")


def _validation() -> ValidationReport:
    def sdp_sos_with_duality():
        for a in A_VALUES:
            p = _p(a)
            res = sos_sdp_certificate(p, [x, y], 1)
            assert res is not None, f"a={a}: SDP refused a valid SOS"
            cert, tight = res
            assert sp.expand(cert.as_expr() - p) == 0            # exact SOS
            # complementary slackness: the square bases' common zero = the tie
            sol = sp.solve([t for t in tight], [x, y], dict=True)
            assert {x: sp.Integer(a), y: sp.Integer(1)} in sol   # tie at (a,1)
    return ValidationReport.from_asserts(
        [("sdp_sos_with_duality", sdp_sos_with_duality)]
    )


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
    print(f"SOSSDP: {res.n_theorems} first-class SDP-SOS certificates "
          f"(interior-tie pencil + duality), hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
