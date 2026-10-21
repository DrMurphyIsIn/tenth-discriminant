"""Zero-free region certificates — Telperion's complex-analytic (Lee-Yang) lens.

Avenue B: instead of bounding logΦ by extremization, locate a ZERO-FREE region of
the complexified partition function (per(L) is exactly such a function); inside
it, logΦ is analytic and Taylor-controlled (Barvinok's interpolation method), and
the tie becomes the NEAREST COMPLEX ZERO -- a Lee-Yang phase transition pinned at
a lattice point rather than an optimum.

The certifiable core is a zero-free DISK by the Rouche dominant-constant-term
bound: p(z) = Σ aₖ zᵏ has NO zero in |z| ≤ r whenever

    |a₀|  >  Σ_{k≥1} |aₖ| rᵏ,

a single exact rational inequality (norm_num).  Its truth implies non-vanishing
in the disk (Rouche: the constant term dominates the rest on |z| = r), hence
analyticity of log p there.  Telperion had no complex-analytic / zero-localization
tooling; this is the entry point.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def dominant_term_margin(coeffs, r: Fr) -> Fr:
    """|a₀| − Σ_{k≥1} |aₖ| rᵏ.  Positive ⟹ p is zero-free in the closed disk
    |z| ≤ r (Rouche).  coeffs = [a₀, a₁, ...] exact rationals (real part of the
    dominance bound; |aₖ| taken as abs)."""
    return abs(coeffs[0]) - sum(abs(coeffs[k]) * r ** k for k in range(1, len(coeffs)))


@dataclass(frozen=True)
class ZeroFreeDiskCertificate:
    """p = Σ aₖ zᵏ zero-free in |z| ≤ r, witnessed by the dominant-term bound."""

    name: str
    coeffs: tuple
    r: Fr

    def check(self) -> bool:
        return dominant_term_margin([Fr(c) for c in self.coeffs], self.r) > 0

    def lean(self) -> str:
        c = [Fr(x) for x in self.coeffs]
        r = self.r
        rhs = sum(abs(c[k]) * r ** k for k in range(1, len(c)))
        a0 = abs(c[0])
        terms = " + ".join(
            f"({abs(c[k]).numerator}/{abs(c[k]).denominator}) * "
            f"({r.numerator}/{r.denominator})^{k}"
            for k in range(1, len(c)) if c[k] != 0
        ) or "0"
        return (
            f"-- {self.name}: p = Σ aₖ zᵏ is ZERO-FREE in |z| ≤ {r} by the Rouche\n"
            f"-- dominant-constant-term bound |a₀| > Σ|aₖ|rᵏ; log p is analytic there\n"
            f"-- (Barvinok interpolation / Lee-Yang).  |a₀| = {a0}, Σ = {rhs}.\n"
            f"theorem {self.name} : ({terms} : ℚ) < {a0.numerator}/{a0.denominator} "
            f":= by norm_num\n"
        )
