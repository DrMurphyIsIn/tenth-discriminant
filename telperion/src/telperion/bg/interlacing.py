"""Root-interlacing certificates — Telperion's real-stability vocabulary.

Log-concavity was all the cavity/potential method had, and we proved no concave
majorant is a super-solution.  Real-stable polynomials carry INTERLACING, which
is strictly stronger and handles non-additive recursions (the tool MSS use, and
the one the Brualdi-Goldwasser telescoping wall structurally lacks).

The certifiable characterization (Hermite-Kakeya-Obreschkoff / Hermite-Biehler):
two real-rooted polynomials p, q interlace iff their WRONSKIAN

    W = p' q - p q'

is SIGN-DEFINITE (never changes sign).  A univariate sign-definite polynomial is
certified by an SOS decomposition -- exactly what Telperion's polynomial-
nonnegativity machinery does.  So an interlacing certificate reduces to: compute
W, and certify +-W >= 0 everywhere via sum-of-squares.  This extends the
`unimodal_certificate` machinery from a single log-concave sequence to the
interlacing of a pair.

The exact-rational engine (roots, Wronskian, SOS) is the untrusted generator;
the Lean kernel checks the emitted `0 <= sum of squares + nonneg const`.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


def wronskian(p: sp.Expr, q: sp.Expr, x: sp.Symbol) -> sp.Expr:
    """W = p' q - p q'.  Sign-definite iff p, q interlace (given real-rooted)."""
    return sp.expand(sp.diff(p, x) * q - p * sp.diff(q, x))


def real_roots(poly: sp.Expr, x: sp.Symbol):
    return sorted(sp.Poly(poly, x).real_roots())


def is_real_rooted(poly: sp.Expr, x: sp.Symbol) -> bool:
    P = sp.Poly(poly, x)
    return len(real_roots(poly, x)) == P.degree()


def interlaces(p: sp.Expr, q: sp.Expr, x: sp.Symbol) -> bool:
    """Exact: p, q both real-rooted and their roots strictly alternate."""
    if not (is_real_rooted(p, x) and is_real_rooted(q, x)):
        return False
    merged = sorted([(r, "p") for r in real_roots(p, x)]
                    + [(r, "q") for r in real_roots(q, x)],
                    key=lambda t: t[0])
    labs = [t for _, t in merged]
    return all(labs[i] != labs[i + 1] for i in range(len(labs) - 1))


def sos_decompose(W: sp.Expr, x: sp.Symbol):
    """Sum-of-squares of a nonneg univariate poly by iterated completing-the-
    square: returns (squares, const) with W == sum(s**2 for s in squares) + const,
    const >= 0.  Requires each leading coefficient a perfect rational square
    (true for the monic Wronskians of monic real-rooted families)."""
    cur = sp.Poly(sp.expand(W), x)
    squares = []
    while cur.degree() >= 2:
        n = cur.degree()
        lc = cur.LC()
        s = sp.sqrt(lc)
        if not s.is_rational:
            raise ValueError(f"leading coeff {lc} not a perfect square; scale first")
        half = n // 2
        b = s * x ** half
        for k in range(1, half + 1):
            target = cur.coeff_monomial(x ** (n - k))
            have = sp.Poly(sp.expand(b ** 2), x).coeff_monomial(x ** (n - k))
            t = sp.nsimplify((target - have) / (2 * s)) if False else (target - have) / (2 * s)
            b = b + t * x ** (half - k)
        b = sp.expand(b)
        squares.append(b)
        cur = sp.Poly(sp.expand(cur.as_expr() - b ** 2), x)
    const = cur.as_expr()
    assert sp.expand(W - (sum(b ** 2 for b in squares) + const)) == 0
    return squares, const


@dataclass(frozen=True)
class InterlacingCertificate:
    """p, q interlace, witnessed by the SOS of the (sign-normalized) Wronskian."""

    name: str
    p: sp.Expr
    q: sp.Expr
    x: sp.Symbol

    def check(self) -> bool:
        return interlaces(self.p, self.q, self.x)

    def lean(self) -> str:
        x = self.x
        W = wronskian(self.p, self.q, x)
        # sign-normalize: certify Wp = +-W >= 0
        s0 = W.subs(x, 0)
        Wp = W if (s0 >= 0) else sp.expand(-W)
        rel = "p' * q - p * q'" if (s0 >= 0) else "p * q' - p' * q"
        squares, const = sos_decompose(Wp, x)

        def _lean(e):  # sympy sstr uses `**`; Lean uses `^`
            return sp.printing.sstr(e).replace("**", "^")

        sos = " + ".join(f"({_lean(b)})^2" for b in squares)
        if const != 0:
            sos += f" + {_lean(const)}"
        wexpr = _lean(Wp)
        return (
            f"-- {self.name}: p, q real-rooted and interlacing  <=>  Wronskian "
            f"({rel}) sign-definite (Hermite-Kakeya-Obreschkoff).\n"
            f"theorem {self.name} : ∀ x : ℝ, (0:ℝ) ≤ {wexpr} := by\n"
            f"  intro x\n"
            f"  have hsos : ({wexpr} : ℝ) = {sos} := by ring\n"
            f"  rw [hsos]; positivity\n"
        )
