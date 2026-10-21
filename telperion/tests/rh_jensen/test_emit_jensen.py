"""Tests for JensenPolynomialHyperbolicityEmitter (Task 5).

conjecture1_proved = False. These tests exercise the d=2 hyperbolicity emitter:
it renders a Lean theorem (from a certified rational coefficient box) that a
degree-2 Jensen polynomial is hyperbolic, and it REFUSES (ValueError) any box
that is not certifiably hyperbolic (margin <= 0) or whose leading coefficient
straddles zero.
"""
import pytest
pytest.importorskip("flint")

from fractions import Fraction as F

from telperion.emit_jensen_polynomial_hyperbolicity import (
    JensenPolynomialHyperbolicityEmitter,
)
from telperion.rh_jensen.jensen import disc2_margin, jensen_coeff_box


def test_emit_produces_lean_theorem():
    box = jensen_coeff_box(n=0, d=2, prec_bits=300)
    assert disc2_margin(box) > 0
    em = JensenPolynomialHyperbolicityEmitter(degree=2)
    text, count = em.render_box(n=0, box=box)
    assert count == 1
    assert "roots.card = 2" in text
    assert "hyperbolic_deg2_of_discrim_nonneg" in text
    assert "jensen_box_hyperbolic_deg2_0" in text


def test_emit_refuses_non_hyperbolic_box():
    # x^2 + 1 style box: c1 = 0, c0 = c2 = 1  => c1^2 - 4 c0 c2 = -4 < 0. Must refuse.
    em = JensenPolynomialHyperbolicityEmitter(degree=2)
    bad_box = [(F(1), F(1)), (F(0), F(0)), (F(1), F(1))]
    with pytest.raises(ValueError):
        em.render_box(n=0, box=bad_box)


def test_emit_refuses_straddling_leading_coeff():
    # Hyperbolic margin (c1 large) but c2 straddles zero -> cannot prove c2 != 0.
    em = JensenPolynomialHyperbolicityEmitter(degree=2)
    straddle_box = [(F(1), F(1)), (F(10), F(10)), (F(-1), F(1))]
    assert disc2_margin(straddle_box) > 0  # margin is fine; only leading-coeff gate should fire
    with pytest.raises(ValueError):
        em.render_box(n=0, box=straddle_box)
