"""Product-telescope closure — the INTEGRATION end of the gauge tower.

The gauge tower has two directions.  UP (differencing / derivation): the curvature quadratic
q(s)=(s+1)(4s+7) has a terminating kinematic tower [q, 8s+15, 8, 0] — this certifies the crossing is
UNIQUE (unimodality).  DOWN (product / integration): the value R(s) is the accumulated product of the
step-ratios, and it TELESCOPES to a closed form — this certifies WHERE the crossing sits and its VALUE.
This module builds the DOWN direction.

THE TELESCOPE.  The step-ratio's curvature factor is a ratio of the SHIFTED potentials
P1(t)=t+1, P2(t)=4t+3:

    1 - 1/q(t) = (q(t)-1)/q(t) = P1(t+1) P2(t) / ( P1(t) P2(t+1) ) ,
      q(t)   = (t+1)(4t+7) = P1(t)  P2(t+1)      (denominator linears)
      q(t)-1 = (t+2)(4t+3) = P1(t+1) P2(t)       (numerator linears)   <- the telescoping key (ring)

so every P1 and P2 appears once forward and once backward and the product collapses:

    PROD_{t=0}^{s-1} (1 - 1/q(t)) = [P1(s)/P1(0)] * [P2(0)/P2(s)] = 3(s+1)/(4s+3) .

Hence the integrated value has a closed form (no residual product):

    R(s) = R(0) * (529/486)^s * (3(s+1)/(4s+3))^11 = (621/64)(529/486)^s (3(s+1)/(4s+3))^11 ,

which reproduces the exact sequence including the resonance R(5)=1 = the integer identity
64*243*23 = 621*576.  Together with the derivation end (UnimodalityCertificate / gauge_lift order-2),
this brackets the near-star from BOTH ends of the tower; their meeting point is the lone integer
identity.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

import sympy as sp

from .bridge import near_star_R


def _P1(t):
    return t + 1


def _P2(t):
    return 4 * t + 3


def q(t):
    """The curvature quadratic q(t) = (t+1)(4t+7) = P1(t) P2(t+1)."""
    return (t + 1) * (4 * t + 7)


@dataclass(frozen=True)
class TelescopeCertificate:
    """The product-telescope of the near-star curvature factor: PROD (1-1/q(t)) = 3(s+1)/(4s+3),
    yielding the closed-form value R(s) whose resonance R(anchor)=1 is the integer identity.
    The integration end of the gauge tower (dual to the differencing/unimodality end)."""

    anchor: int = 5
    reach: int = 3

    # ---- exact engine ------------------------------------------------------
    def telescoped_product(self, s: int) -> Fr:
        """PROD_{t=0}^{s-1} (1 - 1/q(t)), computed directly."""
        p = Fr(1)
        for t in range(s):
            p *= 1 - Fr(1, q(t))
        return p

    def closed_product(self, s: int) -> Fr:
        """The telescoped closed form 3(s+1)/(4s+3)."""
        return Fr(3 * (s + 1), 4 * s + 3)

    def R(self, s: int) -> Fr:
        """R(s) = (621/64)(529/486)^s (3(s+1)/(4s+3))^11 — the integrated closed form."""
        return Fr(621, 64) * Fr(529, 486) ** s * self.closed_product(s) ** 11

    # ---- checks ------------------------------------------------------------
    def telescopes(self) -> bool:
        """The direct product equals the telescoped closed form at every base point."""
        return all(self.telescoped_product(s) == self.closed_product(s)
                   for s in range(0, self.anchor + self.reach + 1))

    def key_identity(self) -> bool:
        """The ring fact that drives the telescope: q(t)-1 = (t+2)(4t+3), q(t) = (t+1)(4t+7),
        with P1, P2 shifting forward by 1 and 4."""
        t = sp.Symbol("t")
        return (sp.expand(q(t) - 1) == sp.expand((t + 2) * (4 * t + 3))
                and sp.expand(q(t)) == sp.expand((t + 1) * (4 * t + 7))
                and sp.expand(_P1(t + 1) - _P1(t)) == 1
                and sp.expand(_P2(t + 1) - _P2(t)) == 4)

    def recovers_closed_form(self) -> bool:
        """R(s) reproduces the exact near-star sequence R_arith = 1/Phi^11."""
        return all(self.R(s) == Fr(sp.Rational(1 / near_star_R(s)))
                   for s in range(0, self.anchor + self.reach))

    def resonance(self) -> bool:
        return self.R(self.anchor) == 1 and 64 * 243 * 23 == 621 * 576

    def check(self) -> bool:
        return (self.key_identity() and self.telescopes()
                and self.recovers_closed_form() and self.resonance())

    # ---- Lean --------------------------------------------------------------
    def lean(self) -> str:
        lines = [
            "-- PRODUCT-TELESCOPE (integration end of the gauge tower).  The curvature factor\n"
            "-- 1 - 1/q(t) = P1(t+1) P2(t) / (P1(t) P2(t+1)),  P1=t+1, P2=4t+3, telescopes:\n"
            "-- PROD_{t<s} (1-1/q(t)) = 3(s+1)/(4s+3), giving the closed form R(s) with R(5)=1.\n"
        ]
        # (1) the telescoping ENGINE — pure ring identities
        lines.append(
            "-- the telescoping key: numerator/denominator of 1-1/q are the shifted potentials.\n"
            "theorem tele_q_factor (t : ℝ) : (t + 1) * (4*t + 7) = 4*t^2 + 11*t + 7 := by ring\n"
            "theorem tele_qm1_factor (t : ℝ) : (t + 1) * (4*t + 7) - 1 = (t + 2) * (4*t + 3) := by ring\n"
            "theorem tele_shift_P1 (t : ℝ) : (t + 1) + 1 = t + 2 := by ring\n"
            "theorem tele_shift_P2 (t : ℝ) : (4*t + 3) + 4 = 4*t + 7 := by ring"
        )
        # (2) the per-step factor identity (division form; field_simp + ring given q != 0)
        lines.append(
            "-- per-step factor as the ratio of shifted potentials (q t ≠ 0).\n"
            "theorem tele_factor (t : ℝ) (hq : (t + 1) * (4*t + 7) ≠ 0) :\n"
            "    1 - 1 / ((t + 1) * (4*t + 7)) = ((t + 2) * (4*t + 3)) / ((t + 1) * (4*t + 7)) := by\n"
            "  field_simp; ring"
        )
        # (3) explicit finite products witnessing the telescoped closed form at each base point
        for s in range(1, self.anchor + self.reach + 1):
            chain = " * ".join(f"(1 - 1/{q(t)})" for t in range(s))
            cp = self.closed_product(s)
            lines.append(
                f"theorem tele_prod_{s} : {chain} = ({cp.numerator}:ℚ)/{cp.denominator} := by norm_num"
            )
        # (4) closed-form recovery + resonance
        for s in range(0, self.anchor + self.reach):
            v = self.R(s)
            cp = self.closed_product(s)
            if v == 1:
                lines.append(
                    f"-- resonance: the integrated value hits 1 at s={s}.\n"
                    f"theorem tele_R_{s} : (621:ℚ)/64 * (529/486)^{s} * "
                    f"(({cp.numerator}:ℚ)/{cp.denominator})^11 = 1 := by norm_num"
                )
            else:
                lines.append(
                    f"theorem tele_R_{s} : (621:ℚ)/64 * (529/486)^{s} * "
                    f"(({cp.numerator}:ℚ)/{cp.denominator})^11 = ({v.numerator}:ℚ)/{v.denominator} := by norm_num"
                )
        lines.append(
            "-- the meeting point of both tower ends: the lone integer identity.\n"
            "theorem tele_resonance_id : (64 * 243 * 23 : ℤ) = 621 * 576 := by norm_num"
        )
        return "\n".join(lines) + "\n"
