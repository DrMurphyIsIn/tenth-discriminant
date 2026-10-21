"""Effective-irrationality-measure attack on the BG <= half -- and its ceiling.

Pins: the effective Liouville bound gives valid, near-saturated STRICTNESS, but is SIGN-BLIND (holds on
both sides of rho_B^n), so it cannot prove the one-sided <= half -- which is a collective positivity, not
a Diophantine approximation. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    IrrationalityCeilingCertificate,
    le_half_holds,
    liouville_lower_bound,
    rho_b_power_11,
)
from telperion.bg.frustration_free import near_star_edges  # noqa: E402
from telperion.bg.sporadic_tie import amp_product  # noqa: E402


def test_liouville_bound_is_valid_and_positive_strictness():
    for s in (2, 3, 4, 6, 7):
        n, e = near_star_edges(s)
        t = amp_product(n, e, 0)
        B = liouville_lower_bound(n, e, 0)
        assert B > 0
        assert (t + B) ** 11 <= rho_b_power_11(n)      # B <= rho_B^n - prod a_v (exact strictness)


def test_le_half_holds_exactly_on_near_stars():
    for s in (2, 3, 4, 6, 7, 8):
        n, e = near_star_edges(s)
        assert le_half_holds(n, e, 0)                  # (prod a)^11 <= (621/64)^n, exact one-sided


def test_measure_is_sign_blind():
    cert = IrrationalityCeilingCertificate()
    assert cert.measure_is_sign_blind()                # rationals bracket rho_B^n; measure holds both sides


def test_certificate_check_and_ceiling_finding():
    cert = IrrationalityCeilingCertificate()
    assert cert.check()
    f = cert.finding()
    assert "SIGN-BLIND" in f
    assert "positivity" in f.lower()
    assert "conjecture1_proved = False" in f
