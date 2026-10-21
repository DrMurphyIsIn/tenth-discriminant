"""Rigorous Li-coefficient enclosures (the li_positivity ladder's Arb backend).

``enclose_li_coeffs`` produces exact-rational outward enclosures of
``taylorCoeff riemannXi n`` (upstream ``LiChallenge/LiCriterion`` convention:
the n-th Maclaurin coefficient of ``logDeriv (phi riemannXi)``, equal to Li's
classical ``λ_{n+1}``) via python-flint ball arithmetic — the same rigor
argument as ``rh_jensen.coefficients`` (module docstring there).

External cross-check: the first three Li–Keiper coefficients are published
(Keiper 1992, Li 1997, Coffey 2004):

    λ₁ ≈ 0.0230957, λ₂ ≈ 0.0923457, λ₃ ≈ 0.2076389

Each test asserts the enclosure CONTAINS the published 7-digit value — an
external anchor, not a comparison against our own output.

conjecture1_proved = False: positive rungs are a necessary-condition check,
not progress toward RH.
"""
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402

pytest.importorskip("flint")

from telperion.li_coeff import enclose_li_coeff, enclose_li_coeffs  # noqa: E402

# Published truncations (7 significant digits) with generous outer slack.
_PUBLISHED = {
    0: Fraction("0.0230957"),   # λ₁
    1: Fraction("0.0923457"),   # λ₂
    2: Fraction("0.2076389"),   # λ₃
}
_SLACK = Fraction(1, 10**6)


def test_enclosures_contain_published_values():
    boxes = enclose_li_coeffs(3, prec_bits=128)
    for n, pub in _PUBLISHED.items():
        lo, hi = boxes[n]
        assert lo - _SLACK <= pub <= hi + _SLACK, (n, lo, hi, pub)
        # And the published value truncations sit INSIDE the rigorous box up to
        # their own truncation error:
        assert hi - lo < Fraction(1, 10**10), "box far wider than expected"


def test_endpoints_are_exact_fractions_and_positive_through_n19():
    boxes = enclose_li_coeffs(20, prec_bits=192)
    assert len(boxes) == 20
    for n, (lo, hi) in enumerate(boxes):
        assert isinstance(lo, Fraction) and isinstance(hi, Fraction)
        assert lo <= hi
        assert lo > 0, f"rung n={n} lower endpoint not positive: {lo}"


def test_single_matches_batch():
    lo_b, hi_b = enclose_li_coeffs(4, prec_bits=128)[3]
    lo_s, hi_s = enclose_li_coeff(3, prec_bits=128)
    assert (lo_s, hi_s) == (lo_b, hi_b)


def test_higher_precision_narrows():
    lo64, hi64 = enclose_li_coeff(0, prec_bits=64)
    lo256, hi256 = enclose_li_coeff(0, prec_bits=256)
    assert hi256 - lo256 < hi64 - lo64
    # Nested consistency: both enclose the same real number.
    assert lo64 <= hi256 and lo256 <= hi64


def test_flint_ctx_is_restored():
    from flint import ctx

    prec_before, cap_before = ctx.prec, ctx.cap
    enclose_li_coeff(1, prec_bits=99)
    assert (ctx.prec, ctx.cap) == (prec_before, cap_before)
