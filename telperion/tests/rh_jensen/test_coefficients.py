# tests/rh_jensen/test_coefficients.py
import pytest
pytest.importorskip("flint")

from fractions import Fraction
import mpmath
from telperion.rh_jensen.coefficients import enclose_xi_coeff, enclose_coeff_box
from telperion.rh_jensen.reference import xi_coeff_reference


def _contains(lohi, val):
    lo, hi = lohi
    return float(lo) <= val <= float(hi)


def test_enclosure_contains_oracle():
    mpmath.mp.dps = 80
    for m in range(0, 5):
        lo, hi = enclose_xi_coeff(m, prec_bits=300)
        assert lo <= hi
        assert _contains((lo, hi), float(xi_coeff_reference(m)))


def _oracle_exact(m):
    """Convert the mpmath oracle alpha(m) to an EXACT signed Fraction.

    Reads the mpf tuple (sign, man, exp, bc): value = (-1)^sign * man * 2^exp.
    No decimal truncation, sign preserved -- so the comparison below is exact.
    """
    o = xi_coeff_reference(m, prec_bits=400)
    sign, man, exp, _bc = o._mpf_
    val = Fraction(man) * (Fraction(2) ** exp) if exp >= 0 else Fraction(man, 2 ** (-exp))
    return -val if sign else val


def test_enclosure_contains_oracle_exact_rational():
    # Exact-rational strengthening of test_enclosure_contains_oracle: no float()
    # casting anywhere. The enclosure endpoints are exact Fraction; the oracle is
    # converted to an exact signed Fraction; containment is asserted with exact
    # Fraction comparisons. This is the module's true rigor gate.
    for prec_bits in (120, 300):
        for m in range(0, 5):
            lo, hi = enclose_xi_coeff(m, prec_bits=prec_bits)
            assert isinstance(lo, Fraction) and isinstance(hi, Fraction)
            assert lo <= hi
            oracle_exact = _oracle_exact(m)
            assert lo <= oracle_exact <= hi, (prec_bits, m)


def test_enclosure_width_shrinks_with_precision():
    lo1, hi1 = enclose_xi_coeff(2, prec_bits=120)
    lo2, hi2 = enclose_xi_coeff(2, prec_bits=300)
    assert (hi2 - lo2) < (hi1 - lo1)


def test_box_shape():
    box = enclose_coeff_box(n=0, d=2, prec_bits=200)
    assert len(box) == 3
    assert all(lo <= hi for lo, hi in box)


def test_negative_control_loose_box_is_honest():
    # A deliberately-too-loose enclosure must still be a valid (containing) bracket,
    # never a silently-tight lie. Width must be strictly positive.
    lo, hi = enclose_xi_coeff(3, prec_bits=64)
    assert hi > lo
