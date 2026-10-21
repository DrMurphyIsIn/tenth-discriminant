"""Mahler measure & the Lehmer gap -- Tier-B research probe #1 for Brualdi-Goldwasser.

TIER_B_TARGETS.md ranks Mahler/Lehmer the STRONGEST structural twin of BG: the Mahler
measure `M(P) = |lead| * prod max(1,|root|) = exp(int_torus log|P|)` is an ARCHIMEDEAN
quantity, yet `M(P) = 1` **iff** `P` is (a monomial times) a product of cyclotomics
(Kronecker) -- a pure INTEGRALITY -- and by Lehmer `M(P)` is either `1` or `>= 1.17628...`
(bounded away).  "`=1` or a gap" is exactly BG's "density `=1` at the tie or strictly below."

**First probe (this module).** Compute `M` of two candidate polynomials over the near-star
family `N(0,s)` (n = 2s+1; the tie is s=5, n=11) and ask: is `M = 1` (cyclotomic) at s=5 and
Lehmer-gapped-away off it?
    (a) the matching polynomial mu(T,x)  (= char poly of the adjacency A, since a tree is a forest)
    (b) the characteristic polynomial of `D + iA`  (Gaussian-integer coefficients)

**HONEST FINDING (negative, and instructive -- this module records WHY).**
Neither candidate realizes the Lehmer picture.  Over s = 2..8 both Mahler measures grow
strictly MONOTONICALLY with s and the tie s=5 is entirely unremarkable:

    s :  2      3      4      5(tie) 6      7      8
    M(mu)      : 3.00   4.00   5.00   6.00   7.01   8.05   9.20     (~ s+1, no dip at s=5)
    M(D+iA)    : 24     108    432    1620   5832   20412  69984    (grows ~ product of degrees)

No `M = 1`, no cyclotomic factor, no gap re-crossing at the tie.  The REASON is diagnostic and
places this probe squarely in an ALREADY-RULED-OUT class (PROOF_STATUS dead-end #2, the
"smooth / archimedean magnitude" refutation): the raw Mahler measure of these polynomials is a
SPECTRAL-RADIUS growth -- `prod max(1,|root|)` tracks the largest adjacency eigenvalue
(`>= sqrt(deg_hub)`), which grows with s -- and it is SEPARABLE over the roots (a product of
per-root factors).  BG's resonance lives only after the arithmetic `(64/621)^n` normalization
and the 11th power that build `Phi^11` (that is what makes `sup density = 1`, reached only at
`11 | n`); a bare Mahler measure carries no such normalization, so it cannot see the tie.

In short: the Lehmer "=1-or-gap" SHAPE is the right analogy, but the matching / `D+iA`
polynomials are the WRONG carriers -- their Mahler measure is archimedean-separable, exactly
the coordinate the audit already refuted.  A live carrier would need `M = 1` to coincide with
the `(64/621)^n`-normalized resonance (e.g. a Mahler measure of an amplitude-derived polynomial
whose cyclotomic locus is the 23-gate); that is left as the frontier, not claimed here.

`conjecture1_proved = False`.  This module is an exact-engine research instrument plus a
reasoned dead-end for the ledger; it proves nothing about BG.
"""
from __future__ import annotations

from dataclasses import dataclass, field

# Lehmer's constant: the smallest known Mahler measure of an integer polynomial that exceeds 1
# (Lehmer's polynomial x^10 + x^9 - x^7 - x^6 - x^5 - x^4 - x^3 + x + 1).  Whether a true gap
# exists above 1 (Lehmer's problem) is open; this is the empirical floor.
LEHMER_CONSTANT = 1.1762808182599175


def mahler_measure(coeffs) -> float:
    """Mahler measure M(P) = |a_n| * prod_i max(1, |root_i|) of a polynomial given as
    coefficients high-degree-to-low (numbers, real or complex).  Numeric (numpy roots)."""
    import numpy as np
    c = [complex(a) for a in coeffs]
    while len(c) > 1 and c[0] == 0:  # strip leading zeros
        c = c[1:]
    if len(c) <= 1:
        return abs(c[0]) if c else 0.0
    roots = np.roots(c)
    lead = abs(c[0])
    prod = 1.0
    for z in roots:
        m = abs(z)
        if m > 1.0:
            prod *= m
    return lead * prod


def _adjacency(n, edges):
    import sympy as sp
    A = sp.zeros(n, n)
    for a, b in edges:
        A[a, b] = 1
        A[b, a] = 1
    return A


def matching_poly(n, edges):
    """The matching polynomial mu(T,x) as a sympy Poly in x.  For a FOREST this equals the
    characteristic polynomial of the adjacency matrix det(xI - A) (Heilmann-Lieb); computed that
    way and cross-checked against graphlimit.matching_polynomial's k-matching counts."""
    import sympy as sp
    x = sp.Symbol("x")
    A = _adjacency(n, edges)
    return sp.Poly(sp.expand((x * sp.eye(n) - A).det()), x)


def matching_poly_from_counts(n, edges):
    """mu(T,x) assembled directly from k-matching counts: sum_k (-1)^k m_k x^(n-2k).  Independent
    of the adjacency-determinant route -- used to VALIDATE matching_poly() on trees."""
    import sympy as sp
    from .graphlimit import matching_polynomial
    x = sp.Symbol("x")
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    counts = matching_polynomial(adj)  # [m_0, m_1, ...] low-to-high in k
    expr = sum((-1) ** k * m * x ** (n - 2 * k) for k, m in enumerate(counts))
    return sp.Poly(sp.expand(expr), x)


def dpa_charpoly(n, edges):
    """Characteristic polynomial det(xI - (D + iA)) as a sympy Poly in x.  D = degree diagonal,
    A = adjacency; coefficients are Gaussian integers (Z[i])."""
    import sympy as sp
    x = sp.Symbol("x")
    A = _adjacency(n, edges)
    degs = [sum(A.row(i)) for i in range(n)]
    D = sp.diag(*degs)
    return sp.Poly(sp.expand((x * sp.eye(n) - (D + sp.I * A)).det()), x)


def is_cyclotomic_product(poly, tol: float = 1e-9) -> bool:
    """Kronecker's theorem test: a monic INTEGER polynomial has Mahler measure 1 iff it is a
    monomial times a product of cyclotomic polynomials.  Returns True iff every non-`x`
    irreducible integer factor of `poly` is a cyclotomic polynomial `Phi_k`.  Returns False for
    non-integer (e.g. Gaussian-integer) coefficients."""
    import sympy as sp
    x = poly.gen
    # integer coefficients only (Kronecker is a Z[x] statement)
    for cf in poly.all_coeffs():
        if not sp.simplify(sp.im(cf)) == 0 or not sp.Rational(cf).is_integer:
            return False
    try:
        _, factors = poly.factor_list()
    except Exception:
        return False
    for f, _mult in factors:
        if f.degree() == 0:
            continue
        if f.as_expr() == x:  # the monomial part
            continue
        d = f.degree()
        # a cyclotomic factor of degree d is Phi_k with euler_phi(k) = d; scan those k
        matched = False
        fm = f.monic().as_expr()
        for k in range(1, 6 * d + 8):
            if sp.totient(k) != d:
                continue
            if sp.expand(fm - sp.cyclotomic_poly(k, x)) == 0:
                matched = True
                break
        if not matched:
            return False
    return True


@dataclass(frozen=True)
class MahlerLehmerProbe:
    """Tier-B probe #1: does a Mahler measure localize the Brualdi-Goldwasser tie?

    Computes M(matching poly) and M(char poly of D+iA) over the near-star family N(0,s) and
    reports the (negative) finding with its reason.  `check()` certifies the INSTRUMENT
    (validated on Lehmer's polynomial and cyclotomics) and the reproducibility of the negative
    result -- NOT the conjecture.  See the module docstring for the full finding."""

    s_values: tuple = (2, 3, 4, 5, 6, 7, 8)
    tie_s: int = 5
    tol: float = 1e-6

    def family_measures(self):
        """List of (s, n, M_matching, M_dpa, matching_is_cyclotomic) over the near-star family."""
        from .matching_free_energy import near_star_edges
        out = []
        for s in self.s_values:
            n, edges = near_star_edges(s)
            mp = matching_poly(n, edges)
            dp = dpa_charpoly(n, edges)
            m_match = mahler_measure([complex(c) for c in mp.all_coeffs()])
            m_dpa = mahler_measure([complex(c) for c in dp.all_coeffs()])
            out.append((s, n, m_match, m_dpa, is_cyclotomic_product(mp)))
        return out

    def matching_poly_route_agrees(self) -> bool:
        """Self-check: the adjacency-determinant matching poly equals the k-matching-count
        assembly for every near-star in the family (validates matching_poly on trees)."""
        from .matching_free_energy import near_star_edges
        for s in self.s_values:
            n, edges = near_star_edges(s)
            if matching_poly(n, edges) != matching_poly_from_counts(n, edges):
                return False
        return True

    def instrument_valid(self) -> bool:
        """Validate the Mahler engine + cyclotomic detector on known values: Lehmer's polynomial
        -> LEHMER_CONSTANT (and NOT cyclotomic); Phi_5 and x^2+x+1 -> M=1 (and cyclotomic)."""
        import sympy as sp
        x = sp.Symbol("x")
        lehmer = [1, 1, 0, -1, -1, -1, -1, -1, 0, 1, 1]
        if abs(mahler_measure(lehmer) - LEHMER_CONSTANT) > 1e-9:
            return False
        if is_cyclotomic_product(sp.Poly(lehmer, x)):
            return False
        for k in (2, 3, 5, 6, 12):
            phi = sp.Poly(sp.cyclotomic_poly(k, x), x)
            if abs(mahler_measure([complex(c) for c in phi.all_coeffs()]) - 1.0) > 1e-6:
                return False
            if not is_cyclotomic_product(phi):
                return False
        return True

    def tie_is_resonant(self) -> bool:
        """Does the tie s=5 uniquely realize the Lehmer picture -- M(matching)=1 (cyclotomic) at
        the tie and gapped-away (>= LEHMER_CONSTANT) at its neighbours?  Observed: False."""
        rows = {s: (m_match, cyc) for s, _n, m_match, _d, cyc in self.family_measures()}
        if self.tie_s not in rows:
            return False
        m_tie, cyc_tie = rows[self.tie_s]
        if not (cyc_tie and abs(m_tie - 1.0) < self.tol):
            return False
        for s in (self.tie_s - 1, self.tie_s + 1):
            if s in rows and rows[s][0] < LEHMER_CONSTANT - self.tol:
                return False
        return True

    def matching_measure_monotone(self) -> bool:
        """The observed structure: M(matching poly) is STRICTLY INCREASING in s (no dip / no
        resonance at the tie) -- the spectral-radius growth that makes this an archimedean,
        already-refuted coordinate."""
        vals = [m_match for _s, _n, m_match, _d, _c in self.family_measures()]
        return all(b > a + self.tol for a, b in zip(vals, vals[1:]))

    def finding(self) -> str:
        rows = self.family_measures()
        m_tie = next((m for s, _n, m, _d, _c in rows if s == self.tie_s), None)
        tie = f"{m_tie:.4f}" if m_tie is not None else "n/a"
        return (
            "NEGATIVE. Neither the matching polynomial nor the char poly of D+iA has Mahler "
            "measure 1 (cyclotomic) at the tie s=5; both grow strictly monotonically in s "
            f"(M(matching) at the tie = {tie}, ~ s+1, no dip). The raw Mahler measure here is a "
            "SPECTRAL-RADIUS growth, SEPARABLE over roots -- the archimedean coordinate the audit "
            "already refuted (PROOF_STATUS dead-end #2). BG's resonance appears only under the "
            "(64/621)^n arithmetic normalization building Phi^11, which a bare Mahler measure "
            "lacks. Right SHAPE (=1-or-gap), wrong CARRIER. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the instrument and the reproducibility of the negative result -- NOT BG.
        True iff: the Mahler/cyclotomic engine is validated on known values, the two matching-poly
        routes agree on every near-star, the tie is NOT resonant, and M(matching) is monotone."""
        return (
            self.instrument_valid()
            and self.matching_poly_route_agrees()
            and not self.tie_is_resonant()
            and self.matching_measure_monotone()
        )
