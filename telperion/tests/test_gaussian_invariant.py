"""Gaussian (Lewis-Riesenfeld) invariant construction tests.

Pins the construction and its two obstructions: the sibling Hessian is rank-1 (symmetric mode only),
and the smooth energy overshoots the continuum (Phi^11 = 1.00046 > 1 between integer trees), so a smooth
Gaussian invariant certifies a FALSE statement. BG is NOT proved; the invariant must be a discrete /
arithmetic Gaussian. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import GaussianInvariantCertificate  # noqa: E402
from telperion.bg.gaussian_invariant import (  # noqa: E402
    SYMMETRIC_MODE_CURVATURE,
    continuum_minimum,
    near_star_energy,
)


def test_tie_on_boundary_but_not_smooth_critical():
    assert abs(near_star_energy(5.0)) < 1e-9                 # x(5) = 0, on the BG boundary
    cert = GaussianInvariantCertificate()
    assert cert.tie_energy_is_zero()
    assert cert.tie_is_not_a_smooth_critical_point()         # x'(5) != 0 -- arithmetic, not smooth, min


def test_continuum_overshoots_phi_above_one():
    sstar, xmin = continuum_minimum()
    assert 4.0 < sstar < 5.0
    assert xmin < 0                                          # continuum dips below the boundary
    over = GaussianInvariantCertificate().continuum_overshoot_amount()
    assert 1.0003 < over < 1.0006                            # Phi^11 ~ 1.00046 > 1 between integers


def test_sibling_hessian_is_rank_one_symmetric_mode():
    assert SYMMETRIC_MODE_CURVATURE == Fr(99, 529)
    assert GaussianInvariantCertificate().sibling_hessian_is_rank_one()


def test_curvature_positive_but_arithmetic_failure():
    cert = GaussianInvariantCertificate()
    assert cert.strict_min_curvature_positive()             # there IS curvature; the failure is arithmetic


def test_certificate_check_and_verdict():
    cert = GaussianInvariantCertificate()
    assert cert.check()
    f = cert.finding()
    assert "NON-SEPARABLE" in f and "INTEGRAL" in f
    assert "conjecture1_proved = False" in f
