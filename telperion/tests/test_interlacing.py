"""Root-interlacing certificate tests."""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    InterlacingCertificate,
    interlaces,
    is_real_rooted,
    sos_decompose,
    wronskian,
)

x = sp.symbols("x")


def test_interlaces_positive():
    assert interlaces(x**2 - 1, x, x)                    # -1 <= 0 <= 1
    assert interlaces(x**3 - 2 * x, x**2 - 1, x)         # matching polys mu(P3)/mu(P2)


def test_interlaces_negative_control():
    assert not interlaces(x**2 - 1, x**2 - 4, x)         # roots don't alternate
    assert not interlaces(x**2 + 1, x, x)                # x^2+1 not real-rooted


def test_wronskian_sign_definite_iff_interlacing():
    # interlacing -> Wronskian sign-definite; non-interlacing -> sign-changing
    W_ok = wronskian(x**3 - 2 * x, x**2 - 1, x)
    assert W_ok == x**4 - x**2 + 2
    W_bad = wronskian(x**2 - 1, x**2 - 4, x)
    assert W_bad == -6 * x                                # changes sign at 0


def test_sos_decompose_exact():
    for W in (x**2 + 1, x**4 - x**2 + 2, x**4 + 1):
        squares, const = sos_decompose(W, x)
        assert sp.expand(W - (sum(b**2 for b in squares) + const)) == 0
        assert const >= 0


def test_certificate_emits_positivity():
    c = InterlacingCertificate("t", x**3 - 2 * x, x**2 - 1, x)
    assert c.check()
    lean = c.lean()
    assert "positivity" in lean and "^" in lean and "**" not in lean


def test_is_real_rooted():
    assert is_real_rooted(x**2 - 1, x)
    assert not is_real_rooted(x**2 + 1, x)
