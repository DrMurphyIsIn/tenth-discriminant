"""Rigorous near-star tail: Phi^11(N(0,s)) <= 1 via the exact cavity rational function.

This proves the surface bound b(s) <= B (equivalently the tail of the legs-2 manifold) RIGOROUSLY, from
the exact cavity form -- no fitting, no transcendental estimate.  The near-star N(0,s) rooted at the hub
has exact amplitudes (fugacity z(d)=3/(3d)=1/d, load 0):

    a_leaf = 1,   a_mid = 1 + (1/2)*1 = 3/2,   a_hub(s) = 1 + (1/(s+1))*s*(1/3) = (4s+3)/(3(s+1)),

    Phi^11(N(0,s)) = (64/621)^(2s+1) * a_hub(s)^11 * (3/2)^(11s)   [VERIFIED vs bg_phi11_fast].

SURFACE BOUND (the b(s) <= B the crossover architecture needs).  With D(s)=Phi^11^(1/(2s+1)) and
D_inf=(64/621)(3/2)^(11/2), the log-surface-coefficient is

    beta(s) := (2s+1)*ln(D(s)/D_inf) = 11*ln(a_hub(s)/sqrt(3/2)),

and since the exact rational a_hub(s)=(4s+3)/(3(s+1)) < 4/3 for ALL s (<=> 12s+9 < 12s+12 <=> 9 < 12),
beta(s) < 11*ln((4/3)/sqrt(3/2)) =: B_log -- a uniform surface bound resting on the trivial fact 9 < 12.

RIGOROUS TAIL (the hard form, no logs).  The exact consecutive ratio is a RATIONAL function

    Q(s) := Phi^11(s+1)/Phi^11(s) = (486/529) * (1 + 1/(4s^2 + 11s + 6))^11,

decreasing in s (the denominator grows), so Q(s) < 1 for all s >= 5 reduces to the single worst case
Q(5) < 1, i.e. the INTEGER inequality

    162^11 * 486  <  161^11 * 529.

Then Phi^11 is decreasing for s >= 5 from Phi^11(5) = 1 (the tie 64*243*23 = 621*576), so Phi^11(s) < 1
for ALL s >= 6; a finite check settles s = 1..4 (< 1) and s = 5 (= 1).  Hence Phi^11(N(0,s)) <= 1 with
equality iff s = 5.

This is the SPIDER-N(0,s) tail only (the extremal manifold's spine).  Competitor extremality (that this
dominates all trees) is the R47 campaign.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def a_hub(s):
    """Exact hub amplitude of N(0,s): (4s+3)/(3(s+1)).  Strictly increasing, bounded above by 4/3."""
    return Fr(4 * s + 3, 3 * (s + 1))


def phi11(s):
    """Exact Phi^11(N(0,s)) = (64/621)^(2s+1) a_hub(s)^11 (3/2)^(11s) (rational; = bg_phi11_fast)."""
    return Fr(64, 621) ** (2 * s + 1) * a_hub(s) ** 11 * Fr(3, 2) ** (11 * s)


def ratio(s):
    """Exact consecutive ratio Q(s) = Phi^11(s+1)/Phi^11(s) = (486/529)(1 + 1/(4s^2+11s+6))^11."""
    return Fr(486, 529) * (1 + Fr(1, 4 * s * s + 11 * s + 6)) ** 11


@dataclass(frozen=True)
class NearStarTailCertificate:
    """Certifies Phi^11(N(0,s)) <= 1 for all s (equality iff s=5) via the exact cavity rational function:
    the surface bound a_hub<4/3, the decreasing rational ratio Q, the crux integer inequality
    162^11*486 < 161^11*529, and a finite check."""

    check_range: int = 60

    def cavity_form_exact(self) -> bool:
        """Phi^11 closed form matches the independent bg_phi11_fast on a range."""
        from .fractal_eigenvalue import near_star_edges
        from .rooted_phi import bg_phi11_fast
        for s in range(1, 24):
            n, e = near_star_edges(s)
            if phi11(s) != bg_phi11_fast(n, e):
                return False
        return True

    def surface_bound(self) -> bool:
        """a_hub(s) < 4/3 for all s (the uniform surface bound core), <=> 9 < 12."""
        return all(a_hub(s) < Fr(4, 3) for s in range(0, self.check_range)) and (9 < 12)

    def crux_integer_inequality(self) -> bool:
        """Q(5) < 1, the single worst case, <=> 162^11 * 486 < 161^11 * 529."""
        return 162 ** 11 * 486 < 161 ** 11 * 529 and ratio(5) < 1

    def ratio_decreasing(self) -> bool:
        """Q is decreasing (4s^2+11s+6 increasing), so Q(s)<1 for all s>=5 follows from Q(5)<1."""
        return all(ratio(s + 1) < ratio(s) for s in range(1, self.check_range)) \
            and all(ratio(s) < 1 for s in range(5, self.check_range))

    def tie_and_finite(self) -> bool:
        """Phi^11(5)=1 (the tie), Phi^11(s)<1 for s in 1..4 and 6..range."""
        if phi11(5) != 1:
            return False
        return all(phi11(s) < 1 for s in list(range(1, 5)) + list(range(6, self.check_range)))

    def check(self) -> bool:
        return (self.cavity_form_exact() and self.surface_bound()
                and self.crux_integer_inequality() and self.ratio_decreasing()
                and self.tie_and_finite())

    def lean(self) -> str:
        return (
            "-- NEAR-STAR TAIL: Phi^11(N(0,s)) <= 1, equality iff s=5, via the exact cavity rational fn.\n"
            "-- Surface bound: a_hub(s)=(4s+3)/(3(s+1)) < 4/3  <=>  9 < 12.\n"
            "-- Ratio Q(s)=(486/529)(1+1/(4s^2+11s+6))^11 decreasing; Q(s)<1 for s>=5 from the CRUX:\n"
            "theorem nearstar_tail_crux : (162^11 * 486 : ℤ) < 161^11 * 529 := by norm_num\n"
            "theorem nearstar_surface_bound (s : ℕ) : (3:ℤ)*(4*s+3) < 4*(3*(s+1)) := by ring_nf; norm_num\n"
            "theorem nearstar_tie_identity : (64 * 243 * 23 : ℤ) = 621 * 576 := by norm_num\n"
        )
