"""Ehrhart / lattice-point probe (Tier-B research target #2) for Brualdi-Goldwasser.

TIER_B_TARGETS.md #2 and ehrhart.py's own moonshot: the modulus 23 is VERIFIED everywhere
(cavity m = 3/23, rho_B^11 = 621/64 = 3^3*23 / 2^6).  If some natural near-star polytope has 23
as its Ehrhart QUASI-POLYNOMIAL PERIOD, the integrality of the tie becomes STRUCTURAL rather than
coincidental -- the only avenue that would say WHY 23.  The `is_quasi_polynomial` / `minimal_period`
primitives already live in `ehrhart.py`; this module supplies the polytope and the exact count.

**Probe (this module).** The fractional matching polytope of `N(0,s)` (the near-star: a hub with s
legs of length 2, n = 2s+1; tie at s=5):
    P(T) = { x_e >= 0 : sum_{e incident to v} x_e <= 1  for every vertex v }.
Its t-dilate lattice-point count `L_P(t) = #(tP cap Z^E)` is computed EXACTLY by a tree-DP (the
constraint graph IS the tree, so a rooted convolution over edge values is exact and polynomial-time).
Feed `L_P` to `minimal_period` over {1, 11, 22, 23, 46}: is the Ehrhart period 23?

**HONEST FINDING (negative, and structural -- this module records WHY).**
Over s = 2..6 the minimal Ehrhart period is **1**: `L_P(t)` is a genuine POLYNOMIAL of degree
E = 2s (e.g. N(0,5): degree 10, leading coeff = volume 1627/518400), NOT a quasi-polynomial.  No
period 11, no period 23.  The reason is a theorem, not a data artifact: a tree is BIPARTITE, so its
matching polytope is INTEGRAL (Edmonds; Birkhoff-von Neumann on the bipartite incidence), and an
integral polytope has Ehrhart PERIOD 1 (Ehrhart's theorem).  The Ehrhart period is the l.c.m. of the
vertex-coordinate denominators of the polytope; integral vertices give denominator 1, so 23 is
structurally unreachable through ANY matching polytope of ANY tree.

A period-23 carrier would need a NON-matching polytope whose vertex denominators are divisible by 23
-- e.g. one built directly from the cavity fixed point `m = 3/23` or the signed lattice-point reading
of the crux deficit `D - N` (Phi^11 = N/D) along the scaling family `n = 11k+1`.  That signed-count
route is exactly the target `ehrhart.py`'s docstring already names; this probe RULES OUT the obvious
matching-polytope realization and redirects there.  (The polytope route does see one structural fact:
`Phi^11(N(0,s)) = 1` exactly at the tie s=5 -- deficit 0 -- but `L_P` is blind to it.)

`conjecture1_proved = False`.  Exact-engine instrument + a reasoned dead-end for the ledger.
"""
from __future__ import annotations

from dataclasses import dataclass


def _tree_adjacency(n, edges):
    adj = {v: [] for v in range(n)}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    if len(edges) != n - 1:
        raise ValueError("matching_polytope_ehrhart expects a tree (E = n - 1)")
    return adj


def matching_polytope_ehrhart(n, edges, T, root: int = 0):
    """Exact Ehrhart data `[L_P(0), ..., L_P(T)]` of the fractional matching polytope of a TREE
    on `n` vertices: `L_P(t) = #{ x in Z_>=0^E : sum_{e at v} x_e <= t for all v }`.

    Computed by a rooted tree-DP: `f_v(p)` = number of consistent assignments in v's subtree given
    the edge from v to its parent carries value `p`, obtained by convolving the children's tables
    under v's own constraint `p + sum(child edge values) <= t`.  Exact (integer) and O(n * t^2)."""
    import sys
    adj = _tree_adjacency(n, edges)
    seq = []
    old_limit = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old_limit, 10 * n + 1000))
    try:
        for t in range(T + 1):
            def f(v, parent):
                # acc[used] = #ways over children processed so far with child-edge sum = used
                acc = [0] * (t + 1)
                acc[0] = 1
                for c in adj[v]:
                    if c == parent:
                        continue
                    fc = f(c, v)  # fc[y] over the (v,c) edge value y in 0..t
                    nacc = [0] * (t + 1)
                    for used in range(t + 1):
                        w = acc[used]
                        if not w:
                            continue
                        for y in range(t + 1 - used):
                            nacc[used + y] += w * fc[y]
                    acc = nacc
                # apply v's constraint p + used <= t: f_v(p) = sum_{used <= t-p} acc[used]
                pref = [0] * (t + 1)
                run = 0
                for k in range(t + 1):
                    run += acc[k]
                    pref[k] = run
                return [pref[t - p] for p in range(t + 1)]
            seq.append(f(root, -1)[0])  # root has no parent edge -> p = 0 (full budget t)
    finally:
        sys.setrecursionlimit(old_limit)
    return seq


def matching_polytope_ehrhart_bruteforce(n, edges, T):
    """Reference lattice-point count by direct enumeration (validates the tree-DP on
    small near-stars).  Same polytope as matching_polytope_ehrhart.

    Counts, for each ``t`` in ``0..T``, the integer points ``x`` in ``[0, t]^|edges|``
    obeying every vertex constraint ``sum_{e ni v} x_e <= t``.  Rather than the naive
    ``product(range(t+1), repeat=|edges|)`` enumerate-all-then-filter (``(t+1)^|edges|``
    points -- ~2e8 at s=4, which times out), this backtracks edge-by-edge and PRUNES a
    partial assignment the moment either endpoint's running sum would exceed ``t``.
    Because ``x >= 0``, a partial sum over ``t`` can never be redeemed, so pruning drops
    only points that fail the filter anyway -- the counted set (hence every ``L_P(t)``)
    is IDENTICAL to the naive enumeration, verified equal on the tractable s=2,3 cases.
    This makes the s=4 reference tractable (~3s vs. a >120s timeout)."""
    ends = [(a, b) for (a, b) in edges]
    E = len(edges)
    seq = []
    for t in range(T + 1):
        vsum = [0] * n
        cnt = 0

        def rec(ei):
            nonlocal cnt
            if ei == E:
                cnt += 1
                return
            a, b = ends[ei]
            hi = t - (vsum[a] if vsum[a] > vsum[b] else vsum[b])
            for val in range(hi + 1):  # val <= hi keeps both endpoints' sums <= t
                vsum[a] += val
                vsum[b] += val
                rec(ei + 1)
                vsum[a] -= val
                vsum[b] -= val

        rec(0)
        seq.append(cnt)
    return seq


@dataclass(frozen=True)
class EhrhartBGProbe:
    """Tier-B probe #2: does the modulus 23 arise as the Ehrhart period of a near-star matching
    polytope?  Computes `L_P(t)` exactly over the near-star family and tests its minimal period.

    `check()` certifies the (true) computed facts -- the matching polytope is integral so the
    minimal Ehrhart period is 1 (never 23), and Phi^11 = 1 at the tie -- NOT the conjecture.
    See the module docstring for the full finding.  conjecture1_proved = False."""

    s_values: tuple = (2, 3, 4, 5, 6)
    tie_s: int = 5
    period_candidates: tuple = (1, 2, 11, 22, 23, 46)

    def _seq_and_deg(self, s):
        from .matching_free_energy import near_star_edges
        n, edges = near_star_edges(s)
        deg = len(edges)              # E = 2s; full-dim polytope -> Ehrhart degree E
        T = deg + 3                   # deg+1 points to fit, >=2 spare to VERIFY (not just interpolate)
        return matching_polytope_ehrhart(n, edges, T), deg

    def family_ehrhart(self):
        """List of (s, n, ehrhart_sequence) over the near-star family."""
        from .matching_free_energy import near_star_edges
        out = []
        for s in self.s_values:
            n, _ = near_star_edges(s)
            seq, _deg = self._seq_and_deg(s)
            out.append((s, n, seq))
        return out

    def minimal_ehrhart_period(self, s):
        """The minimal Ehrhart period of P(N(0,s)) among period_candidates (expected: 1)."""
        from .ehrhart import minimal_period
        seq, deg = self._seq_and_deg(s)
        return minimal_period(seq, self.period_candidates, max_deg=deg)

    def dp_matches_bruteforce(self) -> bool:
        """Self-check: the tree-DP count equals direct enumeration on the small near-stars."""
        from .matching_free_energy import near_star_edges
        for s in (2, 3):
            n, edges = near_star_edges(s)
            T = 2 * s + 2
            if matching_polytope_ehrhart(n, edges, T) != matching_polytope_ehrhart_bruteforce(n, edges, T):
                return False
        return True

    def is_integral_family(self) -> bool:
        """Every near-star matching polytope is integral -> minimal Ehrhart period 1 (a genuine
        polynomial), so 23 never appears as the period."""
        return all(self.minimal_ehrhart_period(s) == 1 for s in self.s_values)

    def deficit_zero_at_tie(self) -> bool:
        """Phi^11(N(0,s)) = 1 exactly at the tie s=5 (the one structural fact the polytope misses)."""
        from .matching_free_energy import near_star_edges
        from .rooted_phi import bg_phi11
        n, edges = near_star_edges(self.tie_s)
        return bg_phi11(n, edges) == 1

    def finding(self) -> str:
        periods = {s: self.minimal_ehrhart_period(s) for s in self.s_values}
        return (
            "NEGATIVE. The fractional matching polytope of every near-star N(0,s) is INTEGRAL "
            "(a tree is bipartite -> Edmonds/Birkhoff), so its Ehrhart count L_P(t) is a genuine "
            f"POLYNOMIAL: minimal period {periods} -- all 1, never 11 or 23. The Ehrhart period is "
            "the lcm of vertex-coordinate denominators; integral vertices give 1, so 23 is "
            "structurally unreachable through any tree matching polytope. A period-23 carrier needs "
            "a non-matching polytope with 23 | vertex denominators (cavity m=3/23, or the signed "
            "D-N count along n=11k+1) -- the redirected frontier. Phi^11=1 holds exactly at the tie "
            "s=5 but L_P is blind to it. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the instrument + the negative result, NOT BG: the tree-DP matches brute force,
        every near-star matching polytope has minimal Ehrhart period 1 (integral; not 23), and
        Phi^11 = 1 at the tie."""
        return (
            self.dp_matches_bruteforce()
            and self.is_integral_family()
            and self.deficit_zero_at_tie()
        )
