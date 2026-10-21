# tests/rh_jensen/test_reference.py
import mpmath
from telperion.rh_jensen.reference import xi_coeff_reference, xi_at_zero_reference


def test_alpha0_equals_xi_half():
    # alpha(0) = Xi(0) = xi(1/2); anchor against a direct zeta/Gamma/pi evaluation.
    mpmath.mp.dps = 60
    xi_half = xi_at_zero_reference()
    alpha0 = xi_coeff_reference(0)
    assert abs(alpha0 - xi_half) < mpmath.mpf(10) ** (-50)


def test_xi_half_direct_value():
    # xi(1/2) = 1/2 * s(s-1) * pi^{-s/2} * Gamma(s/2) * zeta(s) at s = 1/2, positive, ~0.4971207782.
    # NOTE: the brief literal 0.4971207781964073 was incorrect (off by ~8e-11).
    # Recomputed at 50 dps: 0.49712077818831410991...
    mpmath.mp.dps = 40
    val = xi_at_zero_reference()
    assert abs(val - mpmath.mpf("0.4971207781883141099")) < mpmath.mpf(10) ** (-12)
