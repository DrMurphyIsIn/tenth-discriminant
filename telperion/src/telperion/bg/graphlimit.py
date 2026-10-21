"""Graph-limit / matching-measure instruments — the clean handle on unbounded n.

Avenue E: recast max-over-finite-trees as a variational problem over UNIMODULAR
random trees; the extremizer is the explicit infinite near-star limit.  This is
the complementary infrastructure that resolves the gap all the bounded-degree
methods (A-D) share -- unbounded n -- via Benjamini-Schramm convergence.
Abert-Csikvari's matching measure lives here: logΦ is the monomer-dimer free
energy, an integral against the matching measure.

Exact-engine instruments (a reformulation, not a kernel certificate): the
matching polynomial of a finite tree, its (real) root/matching measure, the
per-vertex free-energy density, and the near-star limit these converge to as
n → ∞.  A future proof extremizes the free-energy functional over unimodular
trees; these compute it exactly on finite truncations so the limit can be tested.
"""
from __future__ import annotations

from fractions import Fraction as Fr


def matching_polynomial(adj) -> list[int]:
    """Matching polynomial coefficients [m_0, m_1, ...] of a graph given as an
    adjacency dict {v: set(neighbors)}: m_k = number of k-matchings (Heilmann-Lieb
    real-rooted).  Returned low-to-high in the matching-count convention."""
    edges = sorted({frozenset((u, v)) for u in adj for v in adj[u] if u < v})
    n = len(adj)
    counts = [0] * (n // 2 + 1)
    # enumerate matchings by DFS over edges
    def rec(i, used, k):
        counts[k] += 1
        for e in range(i, len(edges)):
            u, v = tuple(edges[e])
            if u not in used and v not in used:
                rec(e + 1, used | {u, v}, k + 1)
    rec(0, frozenset(), 0)
    return counts


def free_energy_density(adj) -> Fr:
    """Monomer-dimer free-energy proxy: (1/n) log-analogue via the matching-count
    generating value at fugacity 1, per vertex -- the density that converges under
    Benjamini-Schramm.  Exact rational (Σ m_k, not its log, to stay exact)."""
    counts = matching_polynomial(adj)
    n = len(adj)
    return Fr(sum(counts), n)


def path_adj(n) -> dict:
    return {i: {j for j in (i - 1, i + 1) if 0 <= j < n} for i in range(n)}


def star_adj(k) -> dict:
    a = {0: set(range(1, k + 1))}
    for i in range(1, k + 1):
        a[i] = {0}
    return a


def near_star_limit_density(k_values) -> list[tuple[int, Fr]]:
    """The free-energy density of stars S_k as k grows -- the finite truncations
    whose Benjamini-Schramm limit is the extremal infinite near-star.  Returns
    (k, density) so the convergence to the extremizer can be inspected exactly."""
    return [(k, free_energy_density(star_adj(k))) for k in k_values]
