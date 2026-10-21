"""Quantitative 23-gate-strictness bound tests.

Pins: BG = (rational prod a_v) <= (degree-11 algebraic rho_B^n), tie = unique equality (11|n); the exact
deficit integer M and its 23-adic refinement 1-Phi^11 >= 23^{v23(M)}/D; and v23(M)=11(k-1) on the
tie-recursive family. This quantifies STRICTNESS; it does NOT prove the <= half. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    GateStrictnessCertificate,
    deficit_23_valuation,
    deficit_integer,
    rho_b_power_is_rational,
    strictness_bound,
)
from telperion.bg.frustration_free import near_star_edges, tie_recursive_edges  # noqa: E402
from telperion.bg.rooted_phi import bg_phi11_fast  # noqa: E402


def test_equality_needs_11_divides_n():
    assert rho_b_power_is_rational(11) and rho_b_power_is_rational(22)
    assert not rho_b_power_is_rational(7) and not rho_b_power_is_rational(12)


def test_tie_has_zero_deficit_integer():
    n, e = near_star_edges(5)
    M, D = deficit_integer(n, e, 0)
    assert M == 0                                    # tie = exact equality
    for s in (2, 3, 4, 6, 7):
        n, e = near_star_edges(s)
        assert deficit_integer(n, e, 0)[0] >= 1      # non-tie: positive integer deficit numerator


def test_23_refinement_grows_linearly_on_tie_recursive():
    for k in (1, 2, 3, 4, 5):
        n, e = tie_recursive_edges(k)
        assert deficit_23_valuation(n, e, 0) == 11 * (k - 1)


def test_strictness_bound_between_floor_and_actual_deficit():
    for k in (2, 3, 4):
        n, e = tie_recursive_edges(k)
        M, D = deficit_integer(n, e, 0)
        deficit = Fr(1) - bg_phi11_fast(n, e)
        bound = strictness_bound(n, e, 0)
        assert Fr(1, D) <= bound <= deficit          # 1/D  <=  23^{v23}/D  <=  actual deficit
        assert bound > Fr(1, D)                       # strictly refines the crude integrality floor


def test_certificate_check_and_scope():
    cert = GateStrictnessCertificate()
    assert cert.check()
    f = cert.finding()
    assert "does NOT prove the open <= half" in f or "does NOT prove the <= half" in f
    assert "conjecture1_proved = False" in f
