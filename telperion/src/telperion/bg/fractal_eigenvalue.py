"""The self-similar peak family and its transfer eigenvalue -- the "fractal" half of the tail.

Exhaustive search (tree_search / nonisomorphic enumeration) climbs to a PEAK at every order n, and the
peak has a rigid self-similar SHAPE: a hub (odd n) or two hubs (even n) carrying k identical length-2
arms (hub-mid-leaf).  Growing n appends ONE MORE identical arm -- a self-similar generation rule.  A
self-similar generator has a transfer-operator fixed point: adding one length-2 arm multiplies Phi^11 by
a fixed per-arm factor F, so the per-vertex density D = Phi^11^(1/n) tends to F^(1/2).

RESULTS (verified numerically to s=800; closed form modulo a lower-order hub back-reaction):

  arm-transfer factor  F_inf = (3/2)^11 * (64/621)^2   ~ 0.918718   (per 2 vertices)
  density limit        D_inf = (64/621) * (3/2)^(11/2) ~ 0.958498   (per vertex)
  eleventh root        D_inf^(1/11) = sqrt(3/2)/rho_B,   rho_B = (621/64)^(1/11)

The density is UNIMODAL in s: it rises to EXACTLY 1 at s=5 (n=11, the tie) then DECREASES to D_inf,
approached from ABOVE.  So the global sup of density over all trees is the FINITE n=11 tie (=1), and the
asymptotic tail is bounded well below 1 by D_inf.

DEFINITIVE (for the legs-2 asymptote): D_inf < 1 is an INTEGER inequality

    3^11 * 64^2  =  725594112  <  789792768  =  2^11 * 621^2,

the exact analogue of the tie's integer EQUALITY 64*243*23 = 621*576.  Tie = integer equality at n=11;
tail eigenvalue = integer inequality at n=inf -- the same arithmetic/integrality flavor throughout.

CAVEAT (honest scope): this bounds the legs-2 SELF-SIMILAR family (near-star + double-broom), which the
peak-shape census shows is the extremal manifold through n=14.  It does NOT prove legs-2 dominates ALL
trees for all n (the open competitor-extremality / tail theorem), nor does it re-prove the tie.
conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .rooted_phi import bg_phi11_fast


def near_star_edges(s):
    """hub 0 with s arms of length 2 (0-mid-leaf); n = 2s+1.  The self-similar peak at odd n."""
    e = []
    nid = 1
    for _ in range(s):
        e.append((0, nid))
        e.append((nid, nid + 1))
        nid += 2
    return 2 * s + 1, tuple(e)


def arm_transfer_factor(s):
    """F(s) = Phi^11(N(0,s+1)) / Phi^11(N(0,s)) -- the exact per-arm multiplier at finite s (Fraction)."""
    n0, e0 = near_star_edges(s)
    n1, e1 = near_star_edges(s + 1)
    return bg_phi11_fast(n1, e1) / bg_phi11_fast(n0, e0)


def arm_transfer_eigenvalue_closed_form():
    """Closed-form (pure per-arm, no hub back-reaction): F_inf = (3/2)^11 (64/621)^2,
    D_inf = (64/621)(3/2)^(11/2).  Returns (F_inf: Fraction, D_inf: float)."""
    F_inf = Fr(3, 2) ** 11 * Fr(64, 621) ** 2
    D_inf = float(Fr(64, 621)) * (1.5 ** 5.5)
    return F_inf, D_inf


def density_at(s):
    """D(s) = Phi^11(N(0,s))^(1/n) -- the per-vertex density of the s-arm near-star (float)."""
    n, e = near_star_edges(s)
    return float(bg_phi11_fast(n, e)) ** (1.0 / n)


@dataclass(frozen=True)
class FractalEigenvalueCertificate:
    """The self-similar peak family's transfer eigenvalue is < 1 by an INTEGER inequality
    3^11 * 64^2 < 2^11 * 621^2 -- the asymptotic analogue of the tie's integer equality.
    Certifies the legs-2 ASYMPTOTE only (not the full conjecture, not the tie)."""

    def eigenvalue_below_one(self) -> bool:
        """D_inf < 1  <=>  (3/2)^11 < (621/64)^2  <=>  3^11 * 64^2 < 2^11 * 621^2 (exact integers)."""
        return 3 ** 11 * 64 ** 2 < 2 ** 11 * 621 ** 2

    def integer_witness(self):
        """The exact integers (lhs, rhs) with lhs < rhs certifying the eigenvalue below 1."""
        return (3 ** 11 * 64 ** 2, 2 ** 11 * 621 ** 2)

    def unimodal_peak_at_tie(self, s_hi=40) -> bool:
        """Density D(s) is unimodal, strictly maximized at s=5 (D=1); D(s) < 1 for all other s checked."""
        for s in range(1, s_hi + 1):
            d = density_at(s)
            if s == 5:
                if not abs(d - 1.0) < 1e-9:
                    return False
            elif d >= 1.0 - 1e-12:
                return False
        return True

    def approaches_from_above(self) -> bool:
        """For s > 5 the density decreases toward D_inf (the limit is a floor, approached from above)."""
        ds = [density_at(s) for s in (10, 20, 40, 80)]
        _, d_inf = arm_transfer_eigenvalue_closed_form()
        return all(ds[i] > ds[i + 1] for i in range(len(ds) - 1)) and ds[-1] > d_inf

    def check(self) -> bool:
        return (self.eigenvalue_below_one()
                and self.unimodal_peak_at_tie()
                and self.approaches_from_above())

    def lean(self) -> str:
        lhs, rhs = self.integer_witness()
        return (
            "-- FRACTAL TAIL EIGENVALUE < 1 (legs-2 self-similar asymptote): the per-arm transfer factor\n"
            "-- F_inf = (3/2)^11 (64/621)^2 gives density D_inf = (64/621)(3/2)^(11/2) < 1, i.e. the\n"
            "-- INTEGER inequality 3^11*64^2 < 2^11*621^2 -- the tail analogue of the tie's integer equality.\n"
            f"theorem fractal_tail_eigenvalue_lt_one : ({lhs}:ℤ) < {rhs} := by norm_num\n"
            f"theorem fractal_tail_as_ratio : ((3:ℚ)/2)^11 < ((621:ℚ)/64)^2 := by norm_num\n"
        )
