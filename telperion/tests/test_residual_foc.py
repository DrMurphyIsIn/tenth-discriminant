"""Residual FOC bound: closing the interior-max non-arm blocks of single-hub BG.

Pins: the first-order-condition bound Phi^11_hub(k*) <= B_up(k*,mu) (eliminates F_B), which closes every
interior-max non-arm block in the census; the arm as the unique exception (k*=5 > K_max(1/3)=4), proven by
near_star_tail. Remaining gap: no non-arm block has k* > K_max(mu). conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    ResidualFOCCertificate,
    family_argmax,
    family_phi_closed,
    foc_threshold,
    foc_upper_bound,
)


def test_foc_bound_eliminates_F_and_is_valid():
    # at an interior max, Phi^11_hub(k*) <= B_up(k*, mu) (the arm as a concrete check)
    mu, F = Fr(1, 3), Fr(486, 529)
    ks = family_argmax(mu, F)
    assert ks == 5
    assert family_phi_closed(mu, F, ks) <= foc_upper_bound(mu, ks)


def test_foc_threshold_and_arm_exception():
    assert foc_threshold(Fr(1, 3)) == 4                 # B_up(1/3,k) <= 1 for k <= 4
    assert foc_upper_bound(Fr(1, 3), 5) > 1             # arm's k*=5 exceeds it
    assert foc_threshold(Fr(1, 4)) == 22               # smaller message: much larger threshold
    assert 162 ** 11 * 486 < 161 ** 11 * 529            # near_star_tail proves the arm


def test_residual_closed_on_census():
    cert = ResidualFOCCertificate(census_m=9)
    assert cert.foc_bound_is_valid()
    assert cert.foc_closes_the_residual()              # B_up(k*,mu) <= 1 for all interior-max non-arm blocks
    assert cert.residual_gap_is_kstar_below_threshold()


def test_certificate_check_and_scope():
    cert = ResidualFOCCertificate(census_m=8)
    assert cert.check()
    assert cert.arm_is_the_unique_foc_exception()
    f = cert.finding()
    assert "RESIDUAL CLOSED" in f and "near_star_tail" in f
    assert "conjecture1_proved = False" in f
