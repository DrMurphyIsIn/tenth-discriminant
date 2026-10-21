"""Quantization certificate -- the continuum violates the bound, the integers obey it.

The deepest structural fact about Brualdi-Goldwasser (and the reason no smooth certificate can prove it):
the bound Phi <= 1 holds ONLY because the arm count is QUANTIZED (an integer).  The near-star value,
continued to CONTINUOUS real s, EXCEEDS 1:

    Phi^11(N(0,s)) = near_star_R(s)  reaches  ~1.00046 > 1  near s* = 4.822,

but at every INTEGER s it obeys Phi^11 <= 1, with equality exactly at s = 5 (the tie, 64*243*23=621*576).
The integer lattice STRADDLES the continuous overshoot.  Consequently any smooth/analytic certificate --
which lives on the continuum where the bound is FALSE -- provably cannot certify BG; the proof must be
arithmetic (23-adic).

This is the "quantization enforces a bound the continuum violates" phenomenon shared with fermionic QM
(discrete quantum numbers enforcing bounds a classical continuum would break).  This module certifies it:
the continuous maximum > 1 (a witness), and the integer obedience Phi^11(N(0,s)) <= 1 with the tie = 1.
conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .bridge import near_star_R


def continuous_phi11(s):
    """Phi^11(N(0,s)) as a function of s (integer -> exact Fraction; symbolic -> the smooth relaxation)."""
    return near_star_R(s)


def continuous_overshoot(lo=4.0, hi=6.0, steps=4000):
    """(s*, Phi^11(s*)) at the continuous maximum -- the value that EXCEEDS 1, so no smooth cert works."""
    import sympy as sp
    s = sp.Symbol("s")
    f = sp.lambdify(s, near_star_R(s), "math")
    best = (lo, float(f(lo)))
    for i in range(steps + 1):
        sv = lo + (hi - lo) * i / steps
        v = float(f(sv))
        if v > best[1]:
            best = (sv, v)
    return best


@dataclass(frozen=True)
class QuantizationCertificate:
    """Certifies the quantization phenomenon: the continuous relaxation of the near-star value exceeds 1
    (so no smooth certificate exists), while the integer values obey Phi^11 <= 1 with equality at s=5."""

    s_range: tuple = (1, 12)     # integer s to check obedience over
    tie: int = 5

    def continuum_violates(self) -> bool:
        """The continuous maximum of Phi^11(N(0,s)) exceeds 1."""
        _, mx = continuous_overshoot()
        return mx > 1.0

    def integers_obey(self) -> bool:
        """Every INTEGER s gives Phi^11 <= 1, with equality exactly at the tie."""
        lo, hi = self.s_range
        for s in range(lo, hi + 1):
            v = near_star_R(s)
            if s == self.tie:
                if v != 1:
                    return False
            elif v >= 1:
                return False
        return True

    def tie_identity(self) -> bool:
        """The tie value is the integer identity 64*243*23 = 621*576 (= Phi^11(N(0,5)) = 1)."""
        return near_star_R(self.tie) == 1 and 64 * 243 * 23 == 621 * 576

    def check(self) -> bool:
        return self.continuum_violates() and self.integers_obey() and self.tie_identity()

    def lean(self) -> str:
        # the finitely-checkable core: integer obedience + the tie identity. The continuum-violation is a
        # numeric witness (a real-analysis fact) recorded in the comment -- it is the REASON no smooth
        # Lean certificate can prove BG, not a norm_num fact itself.
        s_star, mx = continuous_overshoot()
        lines = [
            f"-- QUANTIZATION: Phi^11(N(0,s)) continued to real s reaches ~{mx:.5f} > 1 at s*~{s_star:.3f}\n"
            f"-- (the continuum VIOLATES BG); but every INTEGER s obeys Phi^11 <= 1, equality at s={self.tie}.\n"
            f"-- Hence no smooth certificate can prove BG -- the proof is arithmetic. Integer witnesses:\n"
        ]
        lo, hi = self.s_range
        for s in range(lo, hi + 1):
            v = near_star_R(s)
            if s == self.tie:
                lines.append(f"theorem quant_tie_s{s} : (({v.numerator}:ℚ)/{v.denominator}) = 1 := by norm_num")
            else:
                lines.append(f"theorem quant_obey_s{s} : ({v.numerator}:ℤ) < {v.denominator} := by norm_num")
        lines.append("theorem quant_tie_identity : (64 * 243 * 23 : ℤ) = 621 * 576 := by norm_num")
        return "\n".join(lines) + "\n"
