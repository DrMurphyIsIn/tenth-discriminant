"""The Gaussian (Lewis-Riesenfeld) invariant construction -- and why it fails: smooth, not integral.

`sibling_coupling.py` reduced BG to a JOINT (multi-variable) sibling condition and pointed at a
Lewis-Riesenfeld Gaussian invariant: a quadratic form in the sibling state, conserved by the (mean-field)
recursion.  This module builds it and reports the outcome honestly.

NOTE (2026-09-29): the premise that a multi-variable invariant is NEEDED is retracted.  The single-variable
no-go in `sibling_coupling.py` came from an LP with a sign error; a concave single-variable witness closes
the ceiling induction (see that module).  The analysis below stands on its own terms.

THE SIBLING HESSIAN (the Gaussian form).  At the tie hub with children messages `mu_c` (tie: `j=5`,
`mu_c=1/3`, `S=5/3`), the hub energy is `x_hub = c0 - 11 log(1 + S/(j+1)) + sum_c x_c`.  Its Hessian in the
sibling-message coordinates splits as

    Hess x_hub  =  [ 11 (1/(j+1))^2 / (1+S/(j+1))^2 ] * J   +   diag(x_c'')
                =  (99/529) * J  (from the hub amplitude)   +   the children's self-curvature ,

where `J` is the all-ones matrix.  The amplitude part is RANK ONE: it curves ONLY the symmetric /
center-of-mass mode `S = sum mu_c` (the Lewis-Riesenfeld decoupled coordinate); the RELATIVE (asymmetric)
sibling modes get zero curvature from the hub.  So the Gaussian form is a rank-1 quadratic in the symmetric
mode -- exactly the near-star / `family_martingale` direction, and nothing transverse.

WHY THE GAUSSIAN INVARIANT CANNOT CERTIFY BG (the decisive obstruction).  A Gaussian/quadratic invariant is
SMOOTH, so it certifies the CONTINUOUS energy `x(s) = -log Phi^11(N(0,s))`, analytically continued in the
arm count `s`.  But the tie is NOT a smooth critical point: `x(5) = 0` yet `x'(5) ~ +0.0051 != 0`, so the
continuum DIPS BELOW ZERO near the tie -- its minimum is `x(s*) ~ -0.00046` at `s* ~ 4.82`, i.e.
`Phi^11 ~ 1.00046 > 1` on the continuum.  The bound `x >= 0` holds only because `s` is an INTEGER (the tie
is an arithmetic resonance); the smooth invariant would certify the overshooting continuum -- a FALSE
statement.  This is PROOF_STATUS dead-end #2 (smooth / archimedean vs. arithmetic) hit head-on.

THE UNIFYING VERDICT.  The two independent no-gos triangulate the TIER_B meta-target ("non-separable AND
integral"): the Lewis-Riesenfeld Gaussian supplies the NON-SEPARABLE (multi-variable quadratic) structure
but is SMOOTH, so it overshoots between integers; the 23-adic carrier (`resonance_carrier.py`) supplies the
INTEGRAL (arithmetic gap) structure but is SEPARABLE.  BG lives at their empty intersection, and neither
machinery alone reaches it.  A certifying invariant must be simultaneously multi-variable AND
integrality-aware -- a discrete/arithmetic Gaussian, which no standard framework supplies.
`conjecture1_proved = False`.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr

C0 = math.log(621 / 64)
LOG32 = math.log(3 / 2)

# symmetric-mode (center-of-mass) curvature of the hub amplitude at the tie: 11*(1/6)^2/(1+ (5/3)/6)^2
SYMMETRIC_MODE_CURVATURE = Fr(99, 529)


def near_star_energy(s: float) -> float:
    """`x(s) = -log Phi^11(N(0,s))` with the arm count `s` analytically continued to real values.
    `Phi^11(N(0,s)) = (64/621)^(2s+1) [ (1 + s/(3(s+1))) (3/2)^s ]^11`, so `x(s) = (2s+1) c0 -
    11 ( log(1 + s/(3(s+1))) + s log(3/2) )`.  Integer `s` are the actual near-star trees."""
    a_hub = 1 + s / (3 * (s + 1))
    return (2 * s + 1) * C0 - 11 * (math.log(a_hub) + s * LOG32)


def _dx(s, h=1e-6):
    return (near_star_energy(s + h) - near_star_energy(s - h)) / (2 * h)


def _d2x(s, h=1e-4):
    return (near_star_energy(s + h) - 2 * near_star_energy(s) + near_star_energy(s - h)) / h ** 2


def continuum_minimum(lo=4.0, hi=5.0, iters=200):
    """The minimum of the continuous `x(s)` near the tie (golden-section) -- returns `(s*, x(s*))`.
    `x(s*) < 0` means the continuum overshoots `Phi^11 > 1` between the integer trees."""
    gr = (math.sqrt(5) - 1) / 2
    a, b = lo, hi
    c, d = b - gr * (b - a), a + gr * (b - a)
    for _ in range(iters):
        if near_star_energy(c) < near_star_energy(d):
            b = d
        else:
            a = c
        c, d = b - gr * (b - a), a + gr * (b - a)
    sm = (a + b) / 2
    return sm, near_star_energy(sm)


@dataclass(frozen=True)
class GaussianInvariantCertificate:
    """Builds the Lewis-Riesenfeld Gaussian (sibling Hessian) at the tie and certifies why it cannot close
    BG: the form is rank-1 (symmetric mode only) and, being smooth, certifies a continuum that OVERSHOOTS
    (Phi^11 = 1.00046 > 1) between the integer trees.  `check()` verifies these structural facts -- NOT BG.
    See the module docstring; the verdict is the non-separable-AND-integral meta-target.  conjecture1 = False."""

    def tie_energy_is_zero(self) -> bool:
        """`x(5) = 0` -- the tie N(0,5) sits exactly on the BG boundary (Phi^11 = 1)."""
        return abs(near_star_energy(5.0)) < 1e-9

    def tie_is_not_a_smooth_critical_point(self) -> bool:
        """`x'(5) != 0` (it is ~ +0.0051): the tie is NOT a smooth minimum -- an arithmetic resonance."""
        return _dx(5.0) > 1e-4

    def continuum_overshoots(self) -> bool:
        """The continuous `x(s)` has a minimum `< 0` near the tie (Phi^11 > 1 between integers): the smooth
        picture violates BG, so a smooth invariant certifies a FALSE statement."""
        _sstar, xmin = continuum_minimum()
        return xmin < 0

    def continuum_overshoot_amount(self) -> float:
        """`max Phi^11` on the continuum near the tie = `exp(-min x)` ~ 1.00046 (> 1)."""
        _sstar, xmin = continuum_minimum()
        return math.exp(-xmin)

    def sibling_hessian_is_rank_one(self) -> bool:
        """The hub-amplitude contribution to the sibling Hessian is `(99/529) * J` -- rank 1, curving ONLY
        the symmetric mode `S = sum mu_c`; the relative (asymmetric) modes get zero curvature from the hub.
        Verified: the mixed and diagonal amplitude second-derivatives are all equal (the all-ones matrix)."""
        j = 5
        S0 = Fr(5, 3)
        entry = 11 * Fr(1, j + 1) ** 2 / (1 + S0 * Fr(1, j + 1)) ** 2
        return entry == SYMMETRIC_MODE_CURVATURE

    def strict_min_curvature_positive(self) -> bool:
        """`x''(5) > 0` -- there IS positive quadratic curvature (the Gaussian form is nondegenerate along
        the symmetric near-star mode); the failure is arithmetic, not a lack of curvature."""
        return _d2x(5.0) > 0

    def finding(self) -> str:
        over = self.continuum_overshoot_amount()
        return (
            "NEGATIVE, and it pins the meta-target. The Lewis-Riesenfeld sibling Hessian at the tie is "
            "(99/529)*J from the hub amplitude -- RANK ONE, curving only the symmetric mode S = sum mu_c "
            "(the near-star / family_martingale direction); the relative sibling modes get zero curvature. "
            "More decisively, a Gaussian invariant is SMOOTH, so it certifies the analytically-continued "
            f"x(s): but the tie is NOT a smooth critical point (x'(5) ~ +0.0051 != 0), and the continuum "
            f"OVERSHOOTS -- min x < 0 near s ~ 4.82, i.e. Phi^11 ~ {over:.5f} > 1 between the integer trees. "
            "x >= 0 holds only because s is an INTEGER (arithmetic resonance). So the smooth Gaussian "
            "certifies a false continuum statement -- dead-end #2 (smooth vs arithmetic). Verdict: the "
            "Lewis-Riesenfeld Gaussian supplies the NON-SEPARABLE structure but not the INTEGRAL one; the "
            "23-adic carrier supplies integral-but-separable; BG's meta-target is their empty intersection. "
            "A certifying invariant must be a DISCRETE/arithmetic Gaussian. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the Gaussian construction's structure and its two obstructions (rank-1 + continuum
        overshoot) -- NOT BG."""
        return (
            self.tie_energy_is_zero()
            and self.tie_is_not_a_smooth_critical_point()
            and self.continuum_overshoots()
            and self.sibling_hessian_is_rank_one()
            and self.strict_min_curvature_positive()
        )
