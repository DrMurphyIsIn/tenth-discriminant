"""Interior-max bound on large-message single-hub families -- tests.

Pins: Phi^11_hub(k) is log-concave in k (sup -> single point); single-copy-dominant blocks are bounded by
the explicit (64/621)(1+mu/2)^11 F_B; and the near-star is the unique equality case, proven by
near_star_tail. Residual (interior-max non-arm blocks) is census-verified < 1. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    InteriorMaxCertificate,
    family_phi,
    is_large_message,
    log_concave_in_k,
    single_copy_value,
)
from telperion.bg.frustration_free import near_star_edges  # noqa: E402


def test_log_concavity_and_single_copy_formula():
    arm = (2, ((0, 1),), 0)
    assert is_large_message(*arm)
    assert log_concave_in_k(*arm)                       # family log-concave in k
    leaf = (1, (), 0)
    assert single_copy_value(*leaf) == family_phi(*leaf, 1)   # explicit k=1 formula matches


def test_near_star_tail_integer_inequality_and_tie():
    assert 162 ** 11 * 486 < 161 ** 11 * 529            # near_star_tail's exact core (proves the arm family)
    arm = (2, ((0, 1),), 0)
    assert family_phi(*arm, 5) == 1                      # near-star tie at k=5 (the unique equality)


def test_arm_is_unique_equality_over_census():
    cert = InteriorMaxCertificate(census_m=6)
    assert cert.arm_is_the_unique_equality()
    assert cert.near_star_tail_proves_the_arm()


def test_certificate_check_and_scope():
    cert = InteriorMaxCertificate(census_m=6)
    assert cert.check()
    assert cert.family_is_log_concave()
    assert cert.single_copy_dominant_are_bounded()
    f = cert.finding()
    assert "LOG-CONCAVE" in f and "near_star_tail" in f
    assert "conjecture1_proved = False" in f
