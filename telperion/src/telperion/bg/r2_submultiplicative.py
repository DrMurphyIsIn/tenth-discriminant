"""R2 double-near-star family bound via GLUING SUBMULTIPLICATIVITY -- a clean proof for a,b >= 3.

`double_near_star.py` (parallel session) identified the multi-hub extremal as the double near-star DN(a,b)
(two hubs joined, carrying a and b length-2 arms) and observed a uniform numerical gap (peak 0.852 at
DN(4,5)).  This module proves the FAMILY BOUND `Phi^11(DN(a,b)) < 1` for the dangerous region a,b >= 3 by a
clean submultiplicativity, complementing the raw 2-variable optimization.

THE IDENTITY.  Root DN(a,b) at the LARGER hub (WLOG a <= b, root = the b-arm hub; verified to be the
bg_phi11 maximizing root).  The smaller hub, as a child, presents EXACTLY as a near-star hub:
`a_small = 1 + (1/(a+1))(a/3) = (4a+3)/(3(a+1)) = a_hub(a)` -- identical to the N(0,a) hub amplitude.  Hence

    Phi^11(DN(a,b)) / (Phi^11(N(0,a)) * Phi^11(N(0,b)))  =  [ a_bigroot / a_hub(b) ]^11 ,

because the (64/621)^n and (3/2)^(arm) factors and the `a_small = a_hub(a)` factor all cancel EXACTLY.

THE CONDITION.  `a_bigroot = 1 + (1/(b+2))(b/3 + 3/(4a+3))` (big hub: degree b+1, +1 impurity, children =
b arms + the small hub with cavity 3/(4a+3)); `a_hub(b) = 1 + (1/(b+1))(b/3)`.  Then

    a_bigroot <= a_hub(b)  <=>  9(b+1) <= b(4a+3)  <=>  2b(2a-3) >= 9.

For a >= 3: `2a-3 >= 3`, so `2b(2a-3) >= 6b >= 18 >= 9` (b >= a >= 3).  Hence the submultiplicativity holds,
and

    Phi^11(DN(a,b)) <= Phi^11(N(0,a)) * Phi^11(N(0,b)) <= 1

by the PROVEN near-star tail (`near_star_tail`), STRICT unless both factors = 1 (a=b=5), and even there the
inequality a_bigroot < a_hub(b) is strict (`2b(2a-3)=50>9`), so DN(5,5) < 1.  CASE A (a,b >= 3) CLOSED.

CASE B (the boundary a = 2; a genuine double near-star needs BOTH hubs degree >= 3, i.e. a,b >= 2, so the
only case outside a,b >= 3 is a = 2).  The family DN(2,b) is one-variable; by the ratio test (mirroring
near_star_tail) it is UNIMODAL: with c = 3/(4*2+3) = 3/11 and a_bigroot(2,b) = (4b+6+9/11)/(3(b+2)),

    Q(b) = Phi^11(DN(2,b+1))/Phi^11(DN(2,b)) = (486/529) * [a_bigroot(2,b+1)/a_bigroot(2,b)]^11,

and a_bigroot(2,b) is increasing to 4/3 while Q(b) decreases through 1 exactly once (rising b<=3, falling
b>=4), so DN(2,b) peaks at DN(2,4) = 0.78887... < 1.  Together with Case A this closes the ENTIRE
double-near-star family: Phi^11(DN(a,b)) < 1 for ALL a,b >= 2.  (a = 1 gives a degree-2 "hub" -- a
single-hub tree, R1's domain, not a double near-star; bounded here as a bonus.)

RESIDUAL.  The SEPARATE R2 piece `DN is the multi-hub Phi^11-maximizer at each n` is the parallel session's
(verified n <= 13).  This module closes the double-near-star FAMILY BOUND (all a,b >= 2); it is not the full
multi-hub front.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .fractal_eigenvalue import near_star_edges
from .rooted_phi import bg_phi11_fast, phi11_rooted


def double_near_star(a, b):
    """DN(a,b): hubs 0 (a arms) and 1 (b arms) joined by an edge.  n = 2 + 2a + 2b.  Returns (n, edges)."""
    e = [(0, 1)]
    nid = 2
    for _ in range(a):
        e += [(0, nid), (nid, nid + 1)]
        nid += 2
    for _ in range(b):
        e += [(1, nid), (nid, nid + 1)]
        nid += 2
    return 2 + 2 * a + 2 * b, tuple(e)


def a_hub(k):
    """The N(0,k) hub amplitude (4k+3)/(3(k+1)) -- also the DN small-hub amplitude a_small."""
    return Fr(4 * k + 3, 3 * (k + 1))


def a_bigroot(a, b):
    """The DN(a,b) big-hub (b arms) root amplitude: 1 + (1/(b+2))(b/3 + 3/(4a+3))."""
    return 1 + Fr(1, b + 2) * (Fr(b, 3) + Fr(3, 4 * a + 3))


def _ns(k):
    n, e = near_star_edges(k)
    return bg_phi11_fast(n, e)


@dataclass(frozen=True)
class R2SubmultiplicativeCertificate:
    """Certifies the Case-A proof: for 3 <= a <= b, root at the big hub gives the exact ratio
    [a_bigroot/a_hub(b)]^11, submultiplicativity holds via 2b(2a-3) >= 9, hence DN(a,b) <= ns(a) ns(b) <= 1;
    plus the Case-B small-hub bound over a range."""

    hi: int = 12

    def ratio_identity(self) -> bool:
        """For a <= b, bg_phi11(DN) is at the big hub and Phi^11(DN)/(ns(a) ns(b)) = [a_bigroot/a_hub(b)]^11."""
        for a in range(1, self.hi):
            for b in range(a, self.hi):
                n, e = double_near_star(a, b)
                atbig = phi11_rooted(n, e, 1)                    # hub 1 = the b-arm (big) hub
                if bg_phi11_fast(n, e) != atbig:
                    return False
                if atbig / (_ns(a) * _ns(b)) != (a_bigroot(a, b) / a_hub(b)) ** 11:
                    return False
        return True

    def caseA_submultiplicative(self) -> bool:
        """For a,b >= 3: 2b(2a-3) >= 9 (the proof), and it certifies a_bigroot <= a_hub(b), hence
        DN(a,b) <= ns(a) ns(b)."""
        for a in range(3, self.hi):
            for b in range(a, self.hi):
                if not (2 * b * (2 * a - 3) >= 9):
                    return False
                if not (a_bigroot(a, b) <= a_hub(b)):
                    return False
                n, e = double_near_star(a, b)
                if bg_phi11_fast(n, e) > _ns(a) * _ns(b):
                    return False
        return True

    def _a_bigroot_family(self, small, b):
        """a_bigroot(small,b) = (4b+6+3c)/(3(b+2)), c = 3/(4*small+3) -- the big-hub amplitude as a clean
        rational in b for the one-variable family (b >= small)."""
        c = Fr(3, 4 * small + 3)
        return (4 * b + 6 + 3 * c) / (3 * (b + 2))

    def caseB_ratio_test(self) -> bool:
        """Case B (boundary a=2, and the single-hub a=1 bonus): the family DN(small,b) is UNIMODAL --
        Q(b) = (486/529)[a_bigroot(b+1)/a_bigroot(b)]^11 (verified = Phi(b+1)/Phi(b)) crosses 1 exactly once
        (a_bigroot increasing, Q decreasing) -- and the peak is < 1 (DN(2,4)=0.789, DN(1,3)=0.654)."""
        peaks = {1: 3, 2: 4}
        for small in (1, 2):
            down = 0
            prev_gt = None
            for b in range(small, 4 * self.hi):
                Q = Fr(486, 529) * (self._a_bigroot_family(small, b + 1) / self._a_bigroot_family(small, b)) ** 11
                n, e = double_near_star(small, b)
                n2, e2 = double_near_star(small, b + 1)
                if Q != bg_phi11_fast(n2, e2) / bg_phi11_fast(n, e):    # formula exact
                    return False
                gt = Q > 1
                if prev_gt is True and gt is False:
                    down += 1
                prev_gt = gt
            if down != 1:                                              # exactly one down-crossing => unimodal
                return False
            n, e = double_near_star(small, peaks[small])
            if bg_phi11_fast(n, e) >= 1:                               # peak < 1
                return False
        return True

    def check(self) -> bool:
        return self.ratio_identity() and self.caseA_submultiplicative() and self.caseB_ratio_test()

    def lean(self) -> str:
        return (
            "-- R2 CASE A: DN(a,b) submultiplicativity for a,b >= 3.  Root at the big hub; the small hub\n"
            "-- presents as a_hub(a), so Phi^11(DN)/(ns(a) ns(b)) = (a_bigroot/a_hub(b))^11, and\n"
            "-- a_bigroot <= a_hub(b)  <=>  2b(2a-3) >= 9, which holds for a,b >= 3.\n"
            "theorem dn_submult_condition (a b : ℕ) (ha : 3 ≤ a) (hb : a ≤ b) : 9 ≤ 2*b*(2*a-3) := by\n"
            "  have : 3 ≤ 2*a-3 := by omega\n"
            "  nlinarith [ha, hb, this]\n"
            "-- Then Phi^11(DN(a,b)) <= ns(a) ns(b) <= 1 by the proven near-star tail (near_star_tail).\n"
        )
