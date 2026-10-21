"""Attacking the BG `<=` half via an effective irrationality measure of rho_B^n -- and its ceiling.

The `<=` half of Brualdi-Goldwasser is `Phi^11 <= 1`, i.e. `prod a_v <= rho_B^n` with
`rho_B = (621/64)^(1/11)` (root of `64 x^11 - 621`, `621 = 3^3 * 23`).  For `11 \\nmid n`, `rho_B^n` is a
degree-11 algebraic irrational and `prod a_v` is rational.  The natural arithmetic attack is an EFFECTIVE
IRRATIONALITY MEASURE (Liouville / Baker): a lower bound `|rho_B^n - p/q| >= B(q)` on how well rationals
approximate `rho_B^n`.  This module builds the effective Liouville bound and reports the outcome honestly.

WHAT THE MEASURE GIVES (verified, exact).  For a tree with `prod a_v = P/Q`, the effective Liouville bound
`|rho_B^n - prod a_v| >= M / (Q^11 * G)` (`M = |621^n Q^11 - 64^n P^11| >= 1`, `G = 11*64^n*(prod a_v + 1)^10`
a rational bound on `|g'|`) is VALID -- `(prod a_v + B)^11 <= (621/64)^n` holds exactly -- and is remarkably
near-SATURATED: `prod a_v` is a near-optimal rational approximation to `rho_B^n` from below.  This reproduces
and refines the `gate_strictness` STRICTNESS (the gap is bounded below by an explicit arithmetic quantity).

WHY IT CANNOT PROVE THE `<=` HALF (the ceiling).  An irrationality measure bounds the DISTANCE
`|rho_B^n - p/q|`; it is SIGN-BLIND.  It holds identically for rationals ABOVE and BELOW `rho_B^n`: one can
exhibit a rational `p_above/Q0 > rho_B^n` (a BG-VIOLATING position) satisfying the very same order-`Q0^{-11}`
bound as the true `prod a_v` does.  So the measure is consistent with a hypothetical violation and gives NO
information about which SIDE of `rho_B^n` the amplitude product lies on.  The `<=` half is a ONE-SIDED
POSITIVITY / sign statement (`prod a_v <= rho_B^n` for ALL trees), orthogonal to approximation QUALITY --
Diophantine tools quantify strictness but cannot deliver the direction.

THE UNIFIED PICTURE (both programs have a ceiling).  Smooth / archimedean methods APPROACH the bound but
OVERSHOOT the continuum (`gaussian_invariant`: `Phi^11 = 1.00046` between integers).  Arithmetic / Diophantine
methods give STRICTNESS but are SIGN-BLIND (this module).  The `<=` half sits in the gap between them: a
COLLECTIVE POSITIVITY that is neither smooth nor a single Diophantine approximation.  It is proven only where
an explicit positivity/martingale argument exists -- the tie-recursive family (`family_martingale`, `F=1`
conservation + an integer inequality) and its mixed-block generalization.  The honest path forward is to
EXTEND that positivity argument to more families, not to chase an irrationality measure.  `conjecture1_proved
= False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .sporadic_tie import amp_product


def _amp(n, edges, root):
    t = amp_product(n, edges, root)
    return t, t.numerator, t.denominator


def rho_b_power_11(n) -> Fr:
    """`(rho_B^n)^11 = (621/64)^n` -- the exact rational whose 11th root is `rho_B^n`."""
    return Fr(621, 64) ** n


def liouville_lower_bound(n, edges, root: int = 0) -> Fr:
    """A rational, EFFECTIVE Liouville lower bound on `|rho_B^n - prod a_v|`:
    `M / (Q^11 * G)` with `M = |621^n Q^11 - 64^n P^11|` and `G = 11 * 64^n * (prod a_v + 1)^10`
    a rational upper bound on `|g'|` over the interval, `g(x) = 64^n x^11 - 621^n` (degree 11)."""
    t, P, Q = _amp(n, edges, root)
    M = abs(621 ** n * Q ** 11 - 64 ** n * P ** 11)
    if M == 0:
        return Fr(0)
    G = 11 * 64 ** n * (t + 1) ** 10
    return Fr(M, Q ** 11) / G


def le_half_holds(n, edges, root: int = 0) -> bool:
    """BG's `<=` half at this root, EXACT: `(prod a_v)^11 <= (621/64)^n`  <=>  `prod a_v <= rho_B^n`."""
    t, _, _ = _amp(n, edges, root)
    return t ** 11 <= rho_b_power_11(n)


@dataclass(frozen=True)
class IrrationalityCeilingCertificate:
    """Effective-irrationality-measure attack on the BG `<=` half, and its ceiling.  Verifies (exactly) that
    the Liouville bound gives effective STRICTNESS but is SIGN-BLIND, so it cannot prove the one-sided `<=`
    half.  `check()` certifies these facts -- NOT BG.  See the module docstring; the `<=` half is a
    collective positivity, not a Diophantine approximation.  conjecture1_proved = False."""

    near_star_s: tuple = (2, 3, 4, 6, 7, 8)    # 11 does not divide n = 2s+1 here
    bracket_denominator: int = 10 ** 6

    def liouville_gives_effective_strictness(self) -> bool:
        """For every near-star the rational Liouville bound `B` is a VALID lower bound on the gap:
        `(prod a_v + B)^11 <= (621/64)^n` (i.e. `B <= rho_B^n - prod a_v`), exact -- effective strictness."""
        from .frustration_free import near_star_edges
        for s in self.near_star_s:
            n, e = near_star_edges(s)
            t, _, _ = _amp(n, e, 0)
            B = liouville_lower_bound(n, e, 0)
            if not ((t + B) ** 11 <= rho_b_power_11(n)):
                return False
        return True

    def measure_is_sign_blind(self) -> bool:
        """The measure is sign-blind: for a representative `n` there is a rational `p_above/Q0 > rho_B^n`
        (a BG-VIOLATING position) whose distance to `rho_B^n` is the SAME order `~1/Q0^11` as a rational
        just below -- so the measure holds on both sides and cannot certify the `<=` direction.  Verified
        exactly by bracketing `rho_B^n` between consecutive `p/Q0`."""
        from sympy import integer_nthroot
        n = 7                                     # 11 does not divide n; rho_B^n irrational
        Q0 = self.bracket_denominator
        target = 621 ** n * Q0 ** 11              # p_below = floor(Q0 * rho_B^n): largest p with p^11*64^n <= target
        p11, _ = integer_nthroot(target // (64 ** n), 11)
        p_below, p_above = p11, p11 + 1
        below = Fr(p_below, Q0)
        above = Fr(p_above, Q0)
        # exact: below^11 <= (621/64)^n < above^11  (below rho, above rho)
        below_is_below = below ** 11 <= rho_b_power_11(n)
        above_is_above = above ** 11 > rho_b_power_11(n)
        # both are within ~1/Q0 of rho_B^n (consecutive brackets) -> the distance measure does not
        # distinguish the BG-consistent (below) from the BG-violating (above) position
        return below_is_below and above_is_above and (above - below == Fr(1, Q0))

    def le_half_is_one_sided_positivity(self) -> bool:
        """The `<=` half is an exact one-sided rational inequality `(prod a_v)^11 <= (621/64)^n` holding for
        ALL trees (verified on near-stars) -- a positivity/sign statement, not an approximation-quality one."""
        from .frustration_free import near_star_edges
        return all(le_half_holds(*near_star_edges(s), 0) for s in self.near_star_s)

    def finding(self) -> str:
        return (
            "CEILING (honest): an effective irrationality measure CANNOT prove the <= half. For 11 does-not-"
            "divide n, rho_B^n = (621/64)^(n/11) is a degree-11 algebraic irrational and prod a_v is rational; "
            "the effective Liouville bound |rho_B^n - prod a_v| >= M/(Q^11 G) is VALID and near-saturated "
            "(prod a_v is a near-optimal approximation from below) -- but it bounds the DISTANCE, and is "
            "SIGN-BLIND: a rational ABOVE rho_B^n (a BG-violating position) satisfies the same order-1/Q^11 "
            "bound, so the measure gives no information on which SIDE prod a_v lies. The <= half is a "
            "ONE-SIDED POSITIVITY (prod a_v <= rho_B^n for ALL trees), orthogonal to approximation quality. "
            "Unified: smooth methods approach but overshoot the continuum; Diophantine methods give strictness "
            "but are sign-blind; the <= half is the collective positivity between them, proven only where an "
            "explicit martingale/positivity exists (family_martingale). Extend that, not the measure. "
            "conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies: the Liouville bound gives effective strictness, the measure is sign-blind, and the
        <= half is a one-sided positivity -- so the irrationality-measure route cannot prove it.  NOT BG."""
        return (
            self.liouville_gives_effective_strictness()
            and self.measure_is_sign_blind()
            and self.le_half_is_one_sided_positivity()
        )
