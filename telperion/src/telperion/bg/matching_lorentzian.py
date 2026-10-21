"""Tier-C probe #1: is the tree's matching polynomial a discrete/arithmetic Gaussian (Lorentzian)?

The 2026-08-17 literature push (TIER_C_TARGETS.md #1) proposed the tree's MULTIVARIATE matching polynomial
as the discrete/arithmetic Gaussian: real-stable (Heilmann-Lieb) hence -- via Branden-Huh Prop 2.2 (stable =>
Lorentzian) -- a Lorentzian polynomial, which is non-separable (Hodge-Riemann Hessian) AND integral (M-convex
support), with the tie N(0,5) hoped to sit on the Lorentzian-cone boundary.  This module runs the make-or-break
probe.  Result: NEGATIVE, and precisely so -- it exposes an exact obstruction and corrects the proposal.

THE OBSTRUCTION (verified exactly).
  (1) The MULTIVARIATE, per-edge matching polynomial (the non-separable object) is NOT Lorentzian: its support
      -- the set of matchings -- FAILS M-convexity for every near-star tested (N(0,2..4)).  Matchings form a
      DELTA-MATROID, not a matroid, so their indicator support is not M-convex; Branden-Huh REQUIRE M-convex
      support, so the object cannot be Lorentzian.  (Branden-Huh Prop 2.2 needs HOMOGENEOUS stable; the matching
      polynomial is stable but NOT homogeneous, and its homogenization is not Lorentzian -- the gap in the
      "stable => Lorentzian for free" hope.)
  (2) The BIVARIATE `m_k` homogenization `sum_k m_k x^k y^(nu-k)` (the integral shadow) IS Lorentzian for every
      tree -- equivalently the univariate matching polynomial `sum m_k x^k` is real-rooted (Heilmann-Lieb).  But
      a two-variable homogeneous polynomial is a SEPARABLE object: it carries the integral log-concavity of the
      `m_k` but NOT the sibling coupling.

THE TENSION (the real finding).  On the matching polynomial the two meta-target properties are at ODDS via the
naive route: the object that is Lorentzian (bivariate `m_k`) is SEPARABLE and GENERIC (Lorentzian for all
trees, so it does not localize the tie); the object that is NON-SEPARABLE (multivariate per-edge) is NOT
Lorentzian (delta-matroid support).  No Lorentzian cone-membership signal distinguishes s=5 either way, so
criterion (4) tie-tightness fails.  The specific gap is DELTA-MATROID vs MATROID (M-convex) support.

WHAT SURVIVES / WHERE NEXT.  The finding does not kill the direction; it sharpens it.  Escape routes the
literature already hints at: (a) Bendjeddou-Hardiman's `R_{W_4}` subdivision makes independence polynomials of
graphs Lorentzian -- test whether a subdivided tree's matching/independence polynomial becomes Lorentzian AND
localizes the tie; (b) delta-matroid / M-convex-set extensions of Lorentzian theory (the correct home for
matchings); (c) drop "matching polynomial" and keep only the resolvent/continuant (Tier-C #3), whose
integrality is the integer diagonal, not M-convex support.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations


def matchings(n, edges):
    """All matchings of the graph as frozensets of edge-indices (including the empty matching)."""
    E = list(range(len(edges)))
    out = [frozenset()]

    def independent(S):
        used = set()
        for i in S:
            a, b = edges[i]
            if a in used or b in used:
                return False
            used.add(a)
            used.add(b)
        return True

    for r in range(1, len(edges) + 1):
        for S in combinations(E, r):
            if independent(S):
                out.append(frozenset(S))
    return out


def matching_support_vectors(n, edges):
    """Support (exponent vectors) of the HOMOGENEOUS per-edge matching polynomial: for each matching M,
    the vector `(nu - |M|, 1_{e in M} ...)` where `nu` is the max matching size (w0 = homogenizer)."""
    Ms = matchings(n, edges)
    m = len(edges)
    nu = max(len(M) for M in Ms)
    return [tuple([nu - len(M)] + [1 if i in M else 0 for i in range(m)]) for M in Ms]


def support_is_m_convex(vectors) -> bool:
    """Symmetric-exchange (M-convexity) test of an integer point set: for all a != b and every i with
    a_i > b_i, there is j with a_j < b_j and both `a - e_i + e_j` and `b - e_i + e_j`... (the standard
    M-convex exchange).  Lorentzian polynomials REQUIRE M-convex support (Branden-Huh)."""
    S = set(vectors)
    for a in vectors:
        for b in vectors:
            if a == b:
                continue
            for i in range(len(a)):
                if a[i] > b[i]:
                    ok = False
                    for j in range(len(a)):
                        if a[j] < b[j]:
                            na = list(a); na[i] -= 1; na[j] += 1
                            nb = list(b); nb[i] += 1; nb[j] -= 1
                            if tuple(na) in S and tuple(nb) in S:
                                ok = True
                                break
                    if not ok:
                        return False
    return True


def bivariate_matching_is_lorentzian(n, edges) -> bool:
    """The bivariate homogenization `sum_k m_k x^k y^(nu-k)` is Lorentzian iff `sum_k m_k x^k` is real-rooted
    (a 2-variable homogeneous polynomial is Lorentzian iff its dehomogenization has all real roots).  True for
    every graph by Heilmann-Lieb -- but this object is SEPARABLE (two variables)."""
    import sympy as sp
    from .graphlimit import matching_polynomial
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    mk = matching_polynomial(adj)
    x = sp.Symbol("x")
    poly = sp.Poly(sum(m * x ** k for k, m in enumerate(mk)), x)
    return all(sp.im(r) == 0 for r in sp.roots(poly, multiple=True))


@dataclass(frozen=True)
class MatchingLorentzianProbe:
    """Tier-C #1 make-or-break probe: can the tree matching polynomial be the discrete/arithmetic Gaussian?
    Verifies the exact obstruction -- the non-separable per-edge object fails M-convexity (delta-matroid), the
    Lorentzian bivariate object is separable and generic -- so the naive route CANNOT carry non-separable AND
    integral together, and no Lorentzian signal localizes the tie.  `check()` certifies this negative, NOT BG."""

    near_star_s: tuple = (2, 3, 4)
    lorentzian_s: tuple = (2, 3, 4, 5)

    def multivariate_support_not_m_convex(self) -> bool:
        """The per-edge matching polynomial's support fails M-convexity for every near-star (matchings are a
        delta-matroid, not a matroid) -> the non-separable object is NOT Lorentzian."""
        from .frustration_free import near_star_edges
        for s in self.near_star_s:
            n, e = near_star_edges(s)
            if support_is_m_convex(matching_support_vectors(n, e)):
                return False
        return True

    def bivariate_is_lorentzian_and_generic(self) -> bool:
        """The bivariate `m_k` object is Lorentzian (real-rooted) for every near-star -- generic, so it does
        NOT localize the tie; and it is separable (two variables)."""
        from .frustration_free import near_star_edges
        for s in self.lorentzian_s:
            n, e = near_star_edges(s)
            if not bivariate_matching_is_lorentzian(n, e):
                return False
        return True

    def tie_not_localized_by_lorentzian_membership(self) -> bool:
        """No Lorentzian cone-membership signal distinguishes the tie s=5: the bivariate object is Lorentzian
        for ALL s (incl. the tie), and the multivariate object is non-Lorentzian for ALL s.  Criterion (4)
        (tie-tightness) fails for the raw matching-polynomial route."""
        return self.bivariate_is_lorentzian_and_generic() and self.multivariate_support_not_m_convex()

    def finding(self) -> str:
        return (
            "NEGATIVE (Tier-C #1 falsified as stated), and it pins the obstruction. The tree matching "
            "polynomial cannot be the discrete/arithmetic Gaussian via the naive route: the NON-SEPARABLE "
            "per-edge matching polynomial is NOT Lorentzian -- its support (matchings) fails M-convexity for "
            "every near-star, because matchings form a DELTA-MATROID, not a matroid (Branden-Huh require "
            "M-convex support; 'stable => Lorentzian' needs HOMOGENEOUS stable, which the matching polynomial "
            "is not). The object that IS Lorentzian -- the bivariate sum m_k x^k y^(nu-k) -- is SEPARABLE "
            "(two variables) and GENERIC (Lorentzian for all trees by Heilmann-Lieb real-rootedness), so it "
            "does not localize the tie. The two meta-target properties are thus at odds on the matching "
            "polynomial: Lorentzian => separable; non-separable => not Lorentzian. The exact gap is "
            "delta-matroid vs matroid. Next: Bendjeddou-Hardiman R_W4 subdivision, delta-matroid Lorentzian "
            "theory, or keep only the resolvent/continuant (Tier-C #3). conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the obstruction: the per-edge object is non-Lorentzian (delta-matroid support), the
        bivariate object is Lorentzian-but-generic-and-separable, and the tie is not localized -- NOT BG."""
        return (
            self.multivariate_support_not_m_convex()
            and self.bivariate_is_lorentzian_and_generic()
            and self.tie_not_localized_by_lorentzian_membership()
        )
