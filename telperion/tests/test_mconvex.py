"""M-convexity (discrete-convex) certificate tests."""
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    MConvexityCertificate,
    is_m_concave,
    is_m_convex,
    separable_concave_on_base,
)


def test_separable_concave_is_m_concave():
    f = separable_concave_on_base(3, 3, lambda t: -t ** 2)
    assert is_m_concave(f)
    assert is_m_convex({k: -v for k, v in f.items()})    # negation is M-convex


def test_non_concave_control_is_not_m_concave():
    f = separable_concave_on_base(3, 3, lambda t: -t ** 2)
    g = {x: Fraction((x[0] * 7 + x[1] * 3) % 5) for x in f}
    assert not is_m_concave(g)


def test_separable_convex_is_not_m_concave():
    # phi(t) = t^2 is CONVEX -> f = Σ t^2 is M-CONVEX, not M-concave
    f = separable_concave_on_base(3, 3, lambda t: t ** 2)
    assert not is_m_concave(f)
    assert is_m_convex(f)


def test_certificate_emits_exchange_inequalities():
    f = separable_concave_on_base(2, 3, lambda t: -t ** 2)
    c = MConvexityCertificate("t", f)
    assert c.check()
    lean = c.lean()
    assert "norm_num" in lean and "exchange" in lean and "≤" in lean


def test_linear_is_m_concave_and_m_convex():
    # linear phi -> f affine -> both M-concave and M-convex (exchange w/ equality)
    f = separable_concave_on_base(2, 3, lambda t: 2 * t)
    assert is_m_concave(f) and is_m_convex(f)
