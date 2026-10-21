# tests/rh_jensen/test_jensen.py
import pytest
pytest.importorskip("flint")

from fractions import Fraction
from telperion.rh_jensen.jensen import jensen_coeff_box, disc2_margin


def test_binomial_scaling():
    box = jensen_coeff_box(n=0, d=2, prec_bits=200)
    assert len(box) == 3  # c0, c1, c2 with weights C(2,0)=1, C(2,1)=2, C(2,2)=1


def test_d2_turan_margin_positive_small_n():
    # The Riemann xi Turan inequalities alpha(n+1)^2 >= alpha(n) alpha(n+2)
    # hold for all n (classical). Margin must certify positive at n = 0.
    box = jensen_coeff_box(n=0, d=2, prec_bits=300)
    m = disc2_margin(box)
    assert m > 0


def test_margin_is_lower_bound():
    # Margin must not exceed the midpoint discriminant (it is a guaranteed lower bound).
    # The true discriminant of a*X^2 + b*X + c (a=c2, b=c1, c=c0) is c1^2 - 4*c0*c2.
    box = jensen_coeff_box(n=1, d=2, prec_bits=300)
    m = disc2_margin(box)
    c0 = (box[0][0] + box[0][1]) / 2
    c1 = (box[1][0] + box[1][1]) / 2
    c2 = (box[2][0] + box[2][1]) / 2
    assert m <= c1 * c1 - 4 * c0 * c2


def test_disc2_margin_refuses_complex_root_box():
    # Adversarial: the point box c0=1, c1=1, c2=0.9 gives 0.9*X^2 + X + 1, whose
    # discriminant is 1 - 4*0.9 = -2.6 < 0 (COMPLEX roots). The margin must be
    # negative (correctly refuse). The old (wrong) c1^2 - c0*c2 = 0.1 > 0 would
    # have falsely certified real-rootedness. This closes that soundness gap.
    box = [
        (Fraction(1), Fraction(1)),
        (Fraction(1), Fraction(1)),
        (Fraction(9, 10), Fraction(9, 10)),
    ]
    m = disc2_margin(box)
    # Exact discriminant: 1 - 4*(9/10) = 1 - 36/10 = -26/10.
    assert m == Fraction(-26, 10)
    assert m < 0


def test_disc2_margin_straddle_zero_c1():
    # Adversarial straddle-zero coverage: c1 in [-1/2, 1/3] straddles 0, so
    # lower(c1^2) = 0. With c0 in [1,1], c2 in [1,1], upper(c0*c2) = 1, so
    # margin = 0 - 4*1 = -4 < 0 (correctly refuses; e.g. X^2 + 0*X + 1 has
    # complex roots).
    box = [
        (Fraction(1), Fraction(1)),
        (Fraction(-1, 2), Fraction(1, 3)),
        (Fraction(1), Fraction(1)),
    ]
    m = disc2_margin(box)
    assert m == Fraction(-4)
    assert m < 0
