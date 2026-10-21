"""Bridge-crossing skill set — integer-Positivstellensatz via finite base + monotone tail.

The unbuilt bridge is: certify a recursively-defined quantity ≤ 1 on ℤ when its
CONTINUOUS relaxation exceeds 1 (the arithmetic tie).  The mechanism that crosses
it -- isolated exactly on the near-star -- is:

  * the continuous violation (a bump) sits in a COMPACT region, bypassed by
    finitely many INTEGER base cases (exact, norm_num);
  * outside that region the quantity is MONOTONE, certified by a smooth tail:
    the ratio R(t+1)/R(t) ≤ 1 for all real t ≥ N, which for the near-star clears
    to a polynomial P(N+u) that has ALL NONNEGATIVE COEFFICIENTS -- Polya-trivial.

Together (base + monotone tail + the anchor R(N) ≤ 1) they give R(n) ≤ 1 for ALL
integers n -- a certificate valid on ℤ though false on ℝ, tight at the integer
tie.  This module builds that composite for the near-star family (crossing the
1-D span of the bridge) and exposes the machinery for the general recursive
profile (recursive_profile), whose crossing needs a FINITE profile -- the open
multivariate research (no finite basis, per the crux map).

This is the design that crosses the bridge; it crosses it fully in 1-D.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

import sympy as sp


def near_star_R(s):
    """R(s) = Φ¹¹ of the near-star N(0, s), exact for integer s, symbolic for a
    symbol.  R(s) = (64/621)^(2s+1) · (3/2)^(11s) · ((4s+3)/(3(s+1)))^11."""
    base = sp.Rational(64, 621) ** (2 * s + 1) * sp.Rational(3, 2) ** (11 * s)
    if isinstance(s, sp.Symbol):
        return base * ((4 * s + 3) / (3 * (s + 1))) ** 11
    return base * sp.Rational(4 * s + 3, 3 * (s + 1)) ** 11


def near_star_tail_poly(anchor: int = 5):
    """The cleared tail inequality ρ(t) = R(t+1)/R(t) ≤ 1 for t ≥ anchor:
    P(anchor+u) = 621²·2^11·[(4t+3)(t+2)]^11 − 64²·3^11·[(4t+7)(t+1)]^11 ≥ 0.
    Returns (P_in_u, all_coeffs_nonneg)."""
    t, u = sp.symbols("t u", nonnegative=True)
    num = (4 * t + 7) * (t + 1)
    den = (4 * t + 3) * (t + 2)
    P = sp.expand(621 ** 2 * 2 ** 11 * den ** 11 - 64 ** 2 * 3 ** 11 * num ** 11)
    Pu = sp.expand(P.subs(t, anchor + u))
    coeffs = sp.Poly(Pu, u).all_coeffs()
    return Pu, all(c >= 0 for c in coeffs)


@dataclass(frozen=True)
class NearStarBridgeCertificate:
    """R(n) ≤ 1 for ALL integers n, via finite base (n = 0..anchor) + the
    all-nonneg-coefficient monotone tail (ρ ≤ 1 for real t ≥ anchor)."""

    anchor: int = 5

    def check(self) -> bool:
        for k in range(self.anchor + 1):
            if near_star_R(k) > 1:
                return False
        if near_star_R(self.anchor) != 1:
            return False
        _, nonneg = near_star_tail_poly(self.anchor)
        return nonneg

    def lean(self) -> str:
        u = sp.Symbol("u")
        Pu, nonneg = near_star_tail_poly(self.anchor)
        assert nonneg
        Pl = sp.printing.sstr(Pu).replace("**", "^")
        lines = [
            f"-- BRIDGE CROSSING (near-star span): R(n) ≤ 1 for ALL integers n,\n"
            f"-- though the continuous relaxation R_cont({4.822:.3f}) = 1.00046 > 1.\n"
            f"-- (1) finite integer base cases n = 0..{self.anchor} (exact);\n"
            f"-- (2) monotone tail: ρ(t) = R(t+1)/R(t) ≤ 1 for real t ≥ {self.anchor},\n"
            f"--     cleared to P({self.anchor}+u) ≥ 0 with ALL NONNEG coefficients (Polya).\n"
            f"-- base + anchor R({self.anchor})=1 + tail-monotonicity ⟹ R(n) ≤ 1 ∀ n ∈ ℤ.\n"
        ]
        for k in range(self.anchor):
            Rk = near_star_R(k)
            lines.append(
                f"theorem near_star_base_{k} : ({Rk.numerator}:ℚ) < {Rk.denominator} := by norm_num"
            )
        Ra = near_star_R(self.anchor)
        lines.append(
            f"theorem near_star_anchor_{self.anchor} : "
            f"(({Ra.numerator}:ℚ)/{Ra.denominator}) = 1 := by norm_num"
        )
        lines.append(
            f"theorem near_star_tail (u : ℝ) (hu : 0 ≤ u) : (0:ℝ) ≤ {Pl} := by positivity"
        )
        return "\n".join(lines) + "\n"
