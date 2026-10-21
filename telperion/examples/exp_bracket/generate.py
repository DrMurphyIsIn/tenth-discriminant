"""Rigorous rational enclosures of exp(-theta) for three rational theta values.

Originally a one-off demonstrator for the far-case threshold constant used in
the origin's R47Encode far predicate.  Promoted to a multi-instance reusable
family flowing through the canonical certify -> emit -> freeze pipeline.

Three instances:
  inst 0 (far-case):  theta = 37167/100000 (the original R47 threshold)
  inst 1 (quarter):   theta = 1/4
  inst 2 (half):      theta = 1/2

Each instance produces two Lean theorems:
  <name>_le:  exp(-theta) <= HI   (Taylor lower bound on exp(theta))
  <name>_ge:  1 - theta   <= exp(-theta)  (convexity companion)

HONEST SCOPE: rigorous rational ENCLOSURES of transcendental constants.
This does NOT close the g1 Real.log bridge (origin's G1Kernel owns it).
conjecture1_proved=False.

Usage: generate.py [--check]
"""
from __future__ import annotations

import argparse
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    GridSpec,
    LeanProfile,
    ValidationReport,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.emit_bracket import BracketSpec, IntervalBracketEmitter, bracket_family

HERE = Path(__file__).resolve().parent


# ---------------------------------------------------------------------------
# Helper: exact rational Taylor sum  sum_{k=0}^{nterms-1} x^k / k!
# ---------------------------------------------------------------------------

def _taylor(x: Fr, nterms: int) -> Fr:
    s, term = Fr(0), Fr(1)
    for k in range(nterms):
        s += term
        term = term * x / (k + 1)
    return s


def _make_spec(theta: Fr, nterms: int, tfloor: Fr, hi: Fr) -> BracketSpec:
    """Construct a BracketSpec using exact Fraction arithmetic for all fields."""
    lo = Fr(1) - theta
    return BracketSpec(
        func="exp",
        theta_num=theta.numerator,
        theta_den=theta.denominator,
        nterms=nterms,
        hi_num=hi.numerator,
        hi_den=hi.denominator,
        lo_num=lo.numerator,
        lo_den=lo.denominator,
        tf_num=tfloor.numerator,
        tf_den=tfloor.denominator,
    )


# ---------------------------------------------------------------------------
# Instance parameters
# ---------------------------------------------------------------------------

# inst 0: far-case (original R47 threshold, preserved semantically)
THETA0 = Fr(37167, 100000)   # 0.37167
NTERMS0 = 9
TFLOOR0 = Fr(145015, 100000)  # clean rational <= Taylor_9(theta0); reduces to 29003/20000
HI0 = Fr(68959, 100000)       # exp(-theta0) <= HI0
SPEC0 = _make_spec(THETA0, NTERMS0, TFLOOR0, HI0)

# inst 1: theta = 1/4
THETA1 = Fr(1, 4)
NTERMS1 = 7
TFLOOR1 = Fr(321, 250)        # <= Taylor_7(1/4)  (1.284 <= 1.284025...)
HI1 = Fr(7789, 10000)         # exp(-1/4) <= HI1
SPEC1 = _make_spec(THETA1, NTERMS1, TFLOOR1, HI1)

# inst 2: theta = 1/2
THETA2 = Fr(1, 2)
NTERMS2 = 9
TFLOOR2 = Fr(16487, 10000)    # <= Taylor_9(1/2)  (1.6487 <= 1.648721...)
HI2 = Fr(30327, 50000)        # exp(-1/2) <= HI2; reduces as-is (gcd=1)
SPEC2 = _make_spec(THETA2, NTERMS2, TFLOOR2, HI2)

# Grid has three points indexed by i in {0, 1, 2}
_SPECS = {0: SPEC0, 1: SPEC1, 2: SPEC2}
_LEAN_NAMES = {
    0: "exp_neg_theta_far",    # the original far-case bound
    1: "exp_neg_quarter",
    2: "exp_neg_half",
}


def _family():
    return bracket_family(
        name="ExpBracket",
        grid=GridSpec([("i", [0, 1, 2])]),
        lean_name=lambda pt: _LEAN_NAMES[pt["i"]],
        spec=lambda pt: _SPECS[pt["i"]],
    )


def _validation() -> ValidationReport:
    def check_all():
        for i, (theta, nterms, tfloor, hi, spec) in enumerate([
            (THETA0, NTERMS0, TFLOOR0, HI0, SPEC0),
            (THETA1, NTERMS1, TFLOOR1, HI1, SPEC1),
            (THETA2, NTERMS2, TFLOOR2, HI2, SPEC2),
        ]):
            T = _taylor(theta, nterms)
            assert tfloor <= T, f"inst {i}: tfloor={tfloor} > Taylor_{nterms}({theta})={T}"
            assert Fr(1) / T <= hi, f"inst {i}: 1/Taylor={Fr(1)/T} > hi={hi}"
            lo = Fr(1) - theta
            v = math.exp(-float(theta))
            assert float(lo) <= v <= float(hi), \
                f"inst {i}: true value {v} not in [{float(lo)}, {float(hi)}]"
            # Verify spec fields round-trip via Fraction
            assert spec.theta == theta
            assert spec.hi == hi
            assert spec.lo == lo
            assert spec.taylor_floor == tfloor

    return ValidationReport.from_asserts([("exp_bracket_all_instances", check_all)])


def build():
    emitter = IntervalBracketEmitter()
    return emit(
        certify(_family()),
        LeanProfile(namespace=("G1", "ExpBracket")),
        [emitter],
        _validation(),
        file_name="ExpBracket.lean",
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
    print(
        f"ExpBracket: {res.n_theorems} theorems, "
        f"{res.n_checks} self-checks, hash {res.input_hash[:16]}\n"
        f"  inst 0 (far-case):  exp(-{float(THETA0):.5f}) in "
        f"[{float(SPEC0.lo):.5f}, {float(SPEC0.hi):.5f}]\n"
        f"  inst 1 (quarter):   exp(-{float(THETA1):.5f}) in "
        f"[{float(SPEC1.lo):.5f}, {float(SPEC1.hi):.5f}]\n"
        f"  inst 2 (half):      exp(-{float(THETA2):.5f}) in "
        f"[{float(SPEC2.lo):.5f}, {float(SPEC2.hi):.5f}]"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
