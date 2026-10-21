"""Lorentzian / Hodge-Riemann certificate + arithmetic-height scaffold tests."""
import sys
from fractions import Fraction
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    HodgeRiemannCertificate,
    displacement_convex,
    global_height_nonneg,
    is_lorentzian_form,
    local_heights,
    signature,
    wasserstein1,
)
from telperion.bg.lorentzian import hessian  # noqa: E402

x1, x2, x3, w1, w2, w3 = sp.symbols("x1 x2 x3 w1 w2 w3")
e2 = x1 * x2 + x1 * x3 + x2 * x3


def test_e2_is_lorentzian():
    H = hessian(e2, [x1, x2, x3])
    assert signature(H) == (1, 0, 2)          # Hodge-index (1, n-1)
    assert is_lorentzian_form(H)


def test_non_lorentzian_rejected():
    # x1^2 + x2^2 has Hessian 2I -> signature (2,0,0), NOT (1,n-1)
    H = hessian(x1**2 + x2**2, [x1, x2])
    assert not is_lorentzian_form(H)


def test_hodge_riemann_certificate():
    c = HodgeRiemannCertificate("t", e2, (x1, x2, x3), (1, 1, 1), (w1, w2, w3))
    assert c.check()
    lean = c.lean()
    assert "positivity" in lean and "**" not in lean and "ring" in lean


def test_hodge_riemann_reverse_cauchy_schwarz_holds():
    # (vᵀHw)² - (vᵀHv)(wᵀHw) >= 0 numerically at random w
    H = hessian(e2, [x1, x2, x3])
    v = sp.Matrix([1, 1, 1])
    for wv in ([1, 0, 0], [2, -1, 3], [1, 1, 1], [0, 5, -2]):
        w = sp.Matrix(wv)
        Q = (v.T * H * w)[0] ** 2 - (v.T * H * v)[0] * (w.T * H * w)[0]
        assert Q >= 0


def test_local_heights_product_formula():
    q = Fraction(64, 621)                      # 64 = 2^6, 621 = 3^3 * 23
    h = local_heights(q, [2, 3, 23])
    # primes in the DENOMINATOR give |q|_p > 1 (positive local height); the prime
    # in the numerator gives |q|_2 < 1 (negative); archimedean is log q < 0.
    assert h[3] > 0 and h[23] > 0 and h[2] < 0 and h["inf"] < 0
    assert global_height_nonneg(q)             # 64/621 <= 1


def test_displacement_convex_checker():
    # a mean-linear functional is displacement-affine (convex, degenerate)
    def mean(mu):
        return sum(p * w for p, w in mu)
    mu0 = [(Fraction(0), Fraction(1))]
    mu1 = [(Fraction(1), Fraction(1))]
    geo = lambda t: [(t, Fraction(1))]
    assert displacement_convex(mean, mu0, mu1, geo)


def test_wasserstein1_exact():
    mu = [(Fraction(0), Fraction(1))]
    nu = [(Fraction(2), Fraction(1))]
    assert wasserstein1(mu, nu) == Fraction(2)
