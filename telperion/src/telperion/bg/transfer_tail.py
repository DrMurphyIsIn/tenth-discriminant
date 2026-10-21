"""Transfer-operator tail bound -- a RESEARCH OBJECT for the open analytic half of Brualdi-Goldwasser.

The tail theorem (OPEN): for all trees with n > N, max_T Phi(T) < 1.  In transfer / tensor-network
language the per-vertex density

    D(T) = Phi^11(T)^(1/n)

IS the dominant eigenvalue of the tree's transfer operator (the bulk free-energy density).  The legs-2
self-similar family (near-star + double-broom) has density UNIMODAL in size: it rises to EXACTLY 1 at the
n=11 tie then DECREASES to the arm-transfer eigenvalue D_inf ~ 0.9585 (= (64/621)(3/2)^(11/2); see
fractal_eigenvalue.py), approached from ABOVE.

CORRECTION 1 (2026-08-17): an earlier version reported a family "limit ~0.964"; that was a FINITE-SIZE
artifact (density at s~80), not the limit.  The true legs-2 limit is D_inf ~0.9585, approached from ABOVE.

CORRECTION 2 (2026-08-17) -- LOAD-BEARING: legs-2 is NOT the density-extremal manifold, and D_inf~0.9585 is
NOT the global sup.  "Hub + k tie-subtrees" (a hub whose every child is a copy of the tie N(0,5)) has
per-vertex density -> 1 (0.9998 at k=400, still climbing), HIGHER than the legs-2 D_inf.  So:
  * D_inf~0.9585 is the near-star FAMILY's OWN limit, NOT a bound over all trees.
  * the SUP of D(T) over all trees is 1 (approached by tie-recursive structures), NOT < 1.
  * therefore the tail is NOT "sup density < c < 1"; the correct statement is:

    tail theorem (open):  D(T) < 1 STRICTLY for every non-tie tree, while sup_T D(T) = 1 is
      APPROACHED (by tie-recursive structures) and REACHED only at integer resonances (11|n + the
      specific tie; see sporadic_tie.py).  Archimedean approach + arithmetic reaching.

So there is NO uniform gap below 1 to lean on -- the bulk+surface/crossover argument bounds the near-star
FAMILY (finite crossover to its own D_inf), NOT arbitrary trees.  The wall is archimedean (density -> 1 as a
growth-rate); the reaching is arithmetic (integrality stops the near-1 structures at 11|n).  This module is
a RESEARCH SCAFFOLD over the legs-2 family only, NOT a global tail certificate.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from .rooted_phi import bg_phi11_fast


def phi_density(n, edges):
    """D(T) = Phi^11(T)^(1/n) -- the per-vertex rooted-Phi density = the transfer dominant eigenvalue."""
    return float(bg_phi11_fast(n, edges)) ** (1.0 / n)


def _edges_of(T):
    idx = {v: i for i, v in enumerate(T.nodes())}
    return T.number_of_nodes(), tuple((idx[a], idx[b]) for a, b in T.edges())


def density_limit(family_fn, sizes):
    """Density of a growing family at each size (the sequence approaches the family's transfer limit).
    `family_fn(size)` returns a networkx tree; returns [(n, D), ...]."""
    out = []
    for s in sizes:
        T = family_fn(s)
        n, e = _edges_of(T)
        out.append((n, phi_density(n, e)))
    return out


@dataclass
class TransferTailBound:
    """Survey the per-vertex density (transfer dominant eigenvalue) over tree families; report the
    empirical sup and frame the open tail theorem.  A research scaffold, not a proof."""

    families: dict = field(default_factory=dict)   # name -> (family_fn, sizes)

    def survey(self):
        """{name: (limit_density, sequence)} for each family; the max limit is the empirical tail sup."""
        res = {}
        for name, (fn, sizes) in self.families.items():
            seq = density_limit(fn, sizes)
            res[name] = (seq[-1][1], seq)
        return res

    def empirical_sup(self):
        """The largest family-limit density among THIS survey's families -- a per-family limit, NOT the
        global sup over all trees.  WARNING: the global sup of D(T) over all trees is 1 (approached by
        tie-recursive structures such as hub+tie-subtrees, density -> 1), NOT the legs-2 D_inf~0.9585."""
        s = self.survey()
        return max(v[0] for v in s.values()) if s else None

    def open_statement(self) -> str:
        return ("TAIL THEOREM (open, CORRECTED): D(T)=Phi^11^(1/n) < 1 STRICTLY for every non-tie tree, "
                "while sup_T D(T) = 1 is APPROACHED (by tie-recursive structures: hub+k tie-subtrees -> 0.9998) "
                "and REACHED only at integer resonances (11|n + the tie; sporadic_tie.py). legs-2 is NOT the "
                "extremal manifold and D_inf~0.9585 is only the near-star FAMILY's limit, NOT the global sup. "
                "The wall is ARCHIMEDEAN (density -> 1 as a growth-rate); the reaching is ARITHMETIC "
                "(integrality). No uniform gap below 1 exists. conjecture1_proved=False.")


def default_families():
    """A standard family set for the survey (near-star, double-broom, comb, path, legs-3)."""
    import networkx as nx

    def spider(s, L=2):
        G = nx.Graph()
        nid = 1
        for _ in range(s):
            p = 0
            for _ in range(L):
                G.add_edge(p, nid)
                p = nid
                nid += 1
        return G

    def double_broom(a):
        G = nx.Graph()
        G.add_edge(0, 1)
        nid = 2
        for h in (0, 1):
            for _ in range(a):
                G.add_edge(h, nid)
                G.add_edge(nid, nid + 1)
                nid += 2
        return G

    def comb(k):
        G = nx.Graph()
        nid = k
        for i in range(k - 1):
            G.add_edge(i, i + 1)
        for i in range(k):
            G.add_edge(i, nid)
            G.add_edge(nid, nid + 1)
            nid += 2
        return G

    return {
        "near_star": (spider, [10, 40, 80]),
        "double_broom": (double_broom, [10, 40, 80]),
        "comb": (comb, [10, 40, 80]),
        "path": (lambda n: nx.path_graph(2 * n + 1), [10, 40, 80]),
        "spider_legs3": (lambda s: spider(s, 3), [10, 40, 80]),
    }
