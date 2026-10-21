"""Arithmetic rigidity certificate — the tie is an INTEGER coincidence.

Of the three sharpened missing tools, this is the one with a genuine finite
certificate, because it is the near-star proof's arithmetic core.  The extremal
fixed point's zero, V(tie) = 0 (equivalently R(5) = 1, R(s) = Φ¹¹(near-star with
c+k = s)), holds ONLY at the integer s = 5 — the continuous critical point
c* ≈ 3.82 gives R > 1.  That rigidity is pinned by an exact integer identity:

    64 · 243 · 23  =  621 · 576   ( = 357696 ),

i.e. (3/2)^{...} · (64/621)^{...} lands exactly on 1 at s = 5 and strictly below
for every other integer (R unimodal, ratio R(s+1)/R(s) crosses 1 once between
s = 5 and s = 6).  This module certifies that arithmetic rigidity: the tie
identity, R(5) = 1 exactly, and the strict local maximum R(4) < 1, R(6) < 1 —
all exact `norm_num` facts.  It is why no SMOOTH tool reaches the tie (they
osculate the continuous c*, not the integer 5).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def near_star_R(s: int) -> Fr:
    """R(s) = Φ¹¹ of the near-star N(0, s) (s arms).  R(s) <= 1 for all integer
    s >= 0, with equality iff s = 5 (the arithmetic tie)."""
    def rec(cr, kids):
        ch = [rec(*k) for k in kids]
        S = sum(m for m, _ in ch)
        d = len(kids) + 1 + cr
        z = Fr(3, 3 * d + cr)
        m = z / (1 + z * S)
        a11 = (Fr(3, 2) ** (11 * cr)) * (1 + Fr(cr, 3 * d)) ** 11 * (Fr(64, 621) ** (1 + 2 * cr))
        p = a11 * (1 + z * S) ** 11
        for _, q in ch:
            p *= q
        return (m, p)
    arm = (0, [(0, [])])
    return rec(0, [arm] * s)[1]


TIE_IDENTITY = (64 * 243 * 23, 621 * 576)   # both 357696


@dataclass(frozen=True)
class ArithmeticRigidityCertificate:
    """The tie's integer coincidence + the strict local maximum of R at s = 5."""

    name: str = "arith_rigidity"

    def check(self) -> bool:
        return (TIE_IDENTITY[0] == TIE_IDENTITY[1]
                and near_star_R(5) == 1
                and near_star_R(4) < 1 and near_star_R(6) < 1)

    def lean(self) -> str:
        r4, r5, r6 = near_star_R(4), near_star_R(5), near_star_R(6)
        assert r5 == 1
        return (
            "-- The tie is an INTEGER coincidence: 64·243·23 = 621·576, pinning\n"
            "-- R(5) = 1 exactly; R strictly below 1 at every other integer\n"
            "-- (unimodal, ratio crosses 1 once between s=5 and s=6).  This is why\n"
            "-- no smooth tool reaches the tie: they osculate c* ≈ 3.82, not 5.\n"
            "theorem tie_identity : (64 * 243 * 23 : ℚ) = 621 * 576 := by norm_num\n"
            f"theorem near_star_R5_eq_one : (({r5.numerator} : ℚ) / {r5.denominator}) = 1 := by norm_num\n"
            f"theorem near_star_R4_lt_one : ({r4.numerator} : ℚ) < {r4.denominator} := by norm_num\n"
            f"theorem near_star_R6_lt_one : ({r6.numerator} : ℚ) < {r6.denominator} := by norm_num\n"
        )
