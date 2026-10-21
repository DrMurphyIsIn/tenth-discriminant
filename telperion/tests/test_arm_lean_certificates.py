"""R1's two scalar inequalities, Lean-tight. Tests (the exact-arithmetic green gate for G1.ArmExtremality).

Pins: the all-nonneg-coefficient Polya tail identity 621(6+k)^11 = 64(7+k)^11 + P(k); the integer descent
tail 64(m+1)^11 <= 621 m^11 (tight at m=6, false at m=4); the base equality B(0,j')=(3/2)^11 and descent
B(L,j')<=(3/2)^11; and the j=2 final rational certificate 64^3*50^11 < 621^3*27^11. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    ArmLeanCertificate,
    TAIL_P_COEFFS,
    arm_B,
    final_rational_certificate,
    per_step_holds,
    tail_identity_holds,
)
from telperion.bg.arm_lean_certificates import GAMMA, W, F_ARM  # noqa: E402


def test_tail_polya_identity_nonneg():
    assert all(c >= 0 for c in TAIL_P_COEFFS)                     # the Polya witness
    assert TAIL_P_COEFFS[-1] == 621 * 6 ** 11 - 64 * 7 ** 11      # constant = tight base
    assert all(tail_identity_holds(k) for k in range(0, 30))     # 621(6+k)^11 = 64(7+k)^11 + P(k)


def test_integer_descent_tail():
    assert per_step_holds(5) and per_step_holds(6)               # holds from m=5 up
    assert not per_step_holds(4)                                  # m>=6 base is not slack (fails at 4)
    assert all(per_step_holds(m) for m in range(6, 300))


def test_base_equality_and_descent():
    assert arm_B(0, 7) == Fr(3, 2) ** 11                          # base equality
    assert arm_B(1, 7) < Fr(3, 2) ** 11                           # strict descent for L>=1
    assert all(arm_B(L, jp) <= Fr(3, 2) ** 11 for jp in range(0, 20) for L in range(0, jp + 1))


def test_j2_final_rational_certificate():
    assert final_rational_certificate()                          # 64^3*50^11 < 621^3*27^11
    assert GAMMA == W ** 2 * Fr(5, 3) ** 11
    assert W * GAMMA ** 2 == W ** 5 * Fr(5, 3) ** 22
    assert W * GAMMA ** 2 < F_ARM
    assert W * GAMMA ** 2 / F_ARM == W ** 3 * Fr(50, 27) ** 11    # cert = W*gamma^2 / (486/529)


def test_certificate_check_and_scope():
    cert = ArmLeanCertificate()
    assert cert.check()
    f = cert.finding()
    assert "64(m+1)^11 <= 621 m^11" in f
    assert "64^3*50^11 < 621^3*27^11" in f
    assert "conjecture1_proved = False" in f
