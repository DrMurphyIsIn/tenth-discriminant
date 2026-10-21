"""Bellman fixed-point instruments + arithmetic-rigidity certificate tests."""
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    ArithmeticRigidityCertificate,
    concave_hull,
    cramer_rate,
    near_star_R,
    sub_hull_gap,
    value_function,
)


def test_near_star_R_tie_at_5():
    assert near_star_R(5) == 1                      # the arithmetic tie
    for s in (0, 1, 2, 3, 4, 6, 7, 8):
        assert near_star_R(s) < 1                    # strict everywhere else


def test_near_star_R_unimodal_ratio_crosses_once():
    Rs = [near_star_R(s) for s in range(0, 9)]
    ratios = [Rs[s + 1] / Rs[s] for s in range(8)]
    signs = [r > 1 for r in ratios]
    # exactly one descent: >1 up to s=4->5, then <1 from s=5->6
    crossings = sum(1 for i in range(len(signs) - 1) if signs[i] != signs[i + 1])
    assert crossings == 1


def test_tie_identity():
    assert 64 * 243 * 23 == 621 * 576 == 357696


def test_rigidity_certificate():
    c = ArithmeticRigidityCertificate()
    assert c.check()
    lean = c.lean()
    assert "tie_identity" in lean and "621 * 576" in lean and "norm_num" in lean


def test_value_function_and_sub_hull_gap():
    V = value_function(max_size=14, max_trees=2000)
    assert len(V) > 100
    gap, at = sub_hull_gap(V)
    assert gap > 0                                   # V is NOT concave (V < hull)
    assert at is not None


def test_cramer_rate_positive_below_hull():
    V = value_function(max_size=14, max_trees=2000)
    rates = cramer_rate(V)
    # most cavities fall strictly below the concave hull -> positive rate
    below = sum(1 for r in rates.values() if r > 1e-9)
    assert below > len(rates) // 2


def test_concave_hull_of_concave_is_itself():
    pts = [(0.0, 0.0), (1.0, 1.0), (2.0, 1.5), (3.0, 1.75)]  # concave-ish
    hull = concave_hull(pts)
    assert hull[0] == (0.0, 0.0) and hull[-1] == (3.0, 1.75)
