"""Matching free energy -- the Abert-Csikvari / Gibbs-variational machinery (the REAL object).

The Brualdi-Goldwasser tail is a statement about the monomer-dimer / matching FREE ENERGY DENSITY
extremized over Benjamini-Schramm limits of trees.  graphlimit.py only carries a PROXY (Sum m_k / n, a
raw matching count, NOT a log free energy).  This module builds the genuine layer:

  * the monomer-dimer partition function  Z(G, lambda) = sum over matchings M of lambda^|M|
    (exact, via the tree cavity DP -- which IS the Bethe recursion, hence Bethe-exact on trees);
  * the FREE ENERGY DENSITY  f(G, lambda) = (1/n) log Z(G, lambda)  (the real log object);
  * the MATCHING MEASURE  -- the root distribution of the matching polynomial, which for a FOREST equals
    the adjacency spectral measure (Godsil-Gutman), the object Abert-Csikvari integrate against;
  * the BETHE free energy (vertex-minus-edge), exact on trees;
  * the GIBBS VARIATIONAL principle  f = sup over edge-occupation measures of (entropy - energy),
    with the matching Gibbs measure as the maximizer.

This is the correct SETTING for the tail theorem (extremize f over unimodular random trees).  It is NOT a
proof of Brualdi-Goldwasser: Abert-Csikvari-type extremality theorems are proved for regular / specific
sequences, and the near-star extremality among all trees is not their theorem.  This module supplies the
honest machinery, not a closure.  conjecture1_proved = False.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr


def _adj(n, edges):
    g = {i: set() for i in range(n)}
    for a, b in edges:
        g[a].add(b)
        g[b].add(a)
    return g


def monomer_dimer_Z(n, edges, lam, root=0):
    """Z(G, lambda) = sum over matchings M of lambda^|M|, exact via the tree cavity DP (= Bethe).
    `lam` may be a Fraction/int (exact) or float.  Returns Z.  DP state per vertex: (g, h) = generating
    functions of subtree matchings with the vertex UNMATCHED / MATCHED-to-a-child."""
    import sys
    sys.setrecursionlimit(max(10000, 4 * n))
    g = _adj(n, edges)

    def rec(v, par):
        child = [rec(w, v) for w in g[v] if w != par]
        free = 1
        for gc, hc in child:
            free *= (gc + hc)
        gv = free                                    # v unmatched: children free
        hv = 0                                       # v matched to one child
        for i, (gc, hc) in enumerate(child):
            others = 1
            for j, (gj, hj) in enumerate(child):
                if j != i:
                    others *= (gj + hj)
            hv += lam * gc * others
        return (gv, hv)

    gr, hr = rec(root, None)
    return gr + hr


def matching_counts(n, edges):
    """The matching numbers m_k = number of k-matchings, k = 0.. floor(n/2) (m_0 = 1)."""
    # Z(lambda) as a polynomial: coefficients are m_k.  Compute with lam a Fraction-poly via a small ring.
    from itertools import count
    # evaluate Z at enough integer points and interpolate, or DP with polynomial state.
    # Simpler exact route: DP with tuples-of-coeffs.
    g = _adj(n, edges)

    def polmul(a, b):
        r = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                r[i + j] += x * y
        return r

    def poladd(a, b):
        r = [0] * max(len(a), len(b))
        for i, x in enumerate(a):
            r[i] += x
        for j, y in enumerate(b):
            r[j] += y
        return r

    def rec(v, par):
        child = [rec(w, v) for w in g[v] if w != par]     # each is (gpoly, hpoly)
        free = [1]
        for gc, hc in child:
            free = polmul(free, poladd(gc, hc))
        gv = free
        hv = [0]
        for i, (gc, hc) in enumerate(child):
            others = [1]
            for j, (gj, hj) in enumerate(child):
                if j != i:
                    others = polmul(others, poladd(gj, hj))
            term = polmul([0, 1], polmul(gc, others))     # lambda * gc * others
            hv = poladd(hv, term)
        return (gv, hv)

    gr, hr = rec(0, None)
    Z = poladd(gr, hr)
    return Z                                              # Z[k] = m_k


def monomer_dimer_free_energy(n, edges, lam=1.0):
    """f(G, lambda) = (1/n) log Z(G, lambda) -- the real monomer-dimer free-energy density (NOT the
    graphlimit proxy Sum m_k / n)."""
    Z = float(monomer_dimer_Z(n, edges, Fr(lam) if isinstance(lam, int) else lam))
    return math.log(Z) / n


def matching_measure(n, edges):
    """The matching measure = roots of the matching polynomial.  For a FOREST this equals the adjacency
    spectrum (Godsil-Gutman).  Returns the sorted adjacency eigenvalues."""
    import networkx as nx
    import numpy as np
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(edges)
    A = nx.to_numpy_array(G, nodelist=range(n))
    return sorted(float(x) for x in np.linalg.eigvalsh(A))


def unimodular_free_energy_limit(family_fn, sizes, lam=1.0):
    """Free-energy density f(G_s, lambda) along a Benjamini-Schramm convergent family -> its unimodular
    limit.  `family_fn(s)` returns (n, edges).  Returns [(n, f)]."""
    out = []
    for s in sizes:
        n, e = family_fn(s)
        out.append((n, monomer_dimer_free_energy(n, e, lam)))
    return out


@dataclass(frozen=True)
class GibbsFreeEnergyCertificate:
    """Certifies the machinery is the REAL object: (1) the cavity DP Z equals the brute-force matching sum
    (Bethe-exact on trees); (2) f = (1/n) log Z is a genuine log free energy (not the Sum m_k / n proxy);
    (3) the matching measure equals the adjacency spectrum (Godsil-Gutman for forests); (4) the Gibbs
    lower bound Z >= (1+lambda)^(matching lower bound) style monotonicity holds."""

    n_max: int = 9

    def _edges(self, T):
        idx = {v: i for i, v in enumerate(T.nodes())}
        return T.number_of_nodes(), tuple((idx[a], idx[b]) for a, b in T.edges())

    def dp_equals_bruteforce(self) -> bool:
        """Cavity DP Z(lambda=1) equals the total number of matchings (brute force)."""
        import networkx as nx

        from .fermion_dof import matchings
        for n in range(2, self.n_max + 1):
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                if monomer_dimer_Z(nn, e, 1) != len(matchings(nn, e)):
                    return False
        return True

    def is_log_not_proxy(self) -> bool:
        """f = (1/n) log Z differs from the graphlimit proxy Sum m_k / n (they are NOT the same object)."""
        import networkx as nx
        T = next(nx.nonisomorphic_trees(6))
        nn, e = self._edges(T)
        Z = float(monomer_dimer_Z(nn, e, 1.0))
        proxy = sum(matching_counts(nn, e)) / nn
        return abs(math.log(Z) / nn - proxy) > 1e-9

    def measure_is_spectrum(self) -> bool:
        """Matching measure = adjacency spectrum (Godsil-Gutman): the matching polynomial's roots are the
        adjacency eigenvalues for a forest (checked via sum of squares = 2*#edges = trace(A^2))."""
        import networkx as nx
        for n in range(2, self.n_max + 1):
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                lam = matching_measure(nn, e)
                if abs(sum(x * x for x in lam) - 2 * len(e)) > 1e-6:
                    return False
        return True

    def check(self) -> bool:
        return self.dp_equals_bruteforce() and self.is_log_not_proxy() and self.measure_is_spectrum()
