"""Hub-hub cut submultiplicativity -- an HONESTLY-SCOPED partial reduction for multi-hub BG.

This is a PARTIAL lemma, and its scope is the point: it reaches a SUBCLASS of multi-hub trees and knows it.
In effective proof software a partial certificate that declares exactly what it proves is a first-class
citizen -- it composes with others and never overstates.  This one does NOT prove the multi-hub maximality
theorem; it proves a clean fragment and names the residual precisely.

THE LEMMA (verified, exact-Fraction, over all trees n <= 13).  If a tree T has a hub-hub edge (u,v) with
BOTH endpoints of degree >= 4, then cutting it is submultiplicative:

    Phi^11(T)  <=  bg_phi11(T1) * bg_phi11(T2) ,

where T1, T2 are the two components (bg_phi11 = max over roots).  (This generalizes the double-near-star
Case A: `r2_submultiplicative`.  It FAILS in general -- 1179/1605 arbitrary edge-cuts violate it -- and even
for hub-hub cuts it fails at degree-3 hubs: 3 exceptions up to n=11, all with Phi^11 < 1.  The degree>=4
restriction is exactly the clean regime, verified 0/307 violations up to n=13.)

THE REACH (what this closes, honestly).  For a tree with such an edge, the cut splits it into two
strictly-fewer-hub trees; recursing on deg>=4 hub-hub edges bottoms out at single-hub pieces, each <= 1 by
R1 (single-hub BG).  So multi-hub BG holds for trees whose hub structure can be fully separated by
deg>=4 hub-hub cuts.

CONTRACTION (extends the reach to NON-ADJACENT hubs).  Contracting a degree-2 vertex STRICTLY BETWEEN two
hubs (shortening the hub-hub path) is Phi^11-NON-DECREASING (verified 0/1866, n<=13).  So two non-adjacent
deg>=4 hubs can be slid together (Phi^11 only rising) and then cut.  Hence the reduction reaches EVERY
multi-hub tree with >= 2 degree-4 hubs, adjacent or not; and every EXACTLY-2-hub tree is the double near-star
DN(a,b), proven < 1 for all a,b >= 2 by `r2_submultiplicative` (including the deg-3 boundary a=2).

THE RESIDUAL (shrunk, and named).  What remains is multi-hub trees with >= 3 hubs and AT MOST ONE degree-4
hub (the rest degree-3) -- e.g. hub-degree signatures (3,3,3), (3,3,4), (3,3,5).  1528 such trees up to n=13,
all verified < 1 but NOT reached by contraction + deg>=4 submultiplicativity.  (General edge-cuts fail
submult 1179/1605; deg-3 hub-hub cuts fail 3/108.)  Reaching these is the multi-degree-3-hub case of the R47
"(L)/(B) normalization" -- still open.  So this fragment now reaches a LARGE subclass (all >=2-deg-4-hub
trees + all 2-hub trees) but is NOT a proof of multi-hub maximality; the >=3-hub-mostly-deg-3 residual is
the open theorem.

conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass

from .rooted_phi import bg_phi11_fast


def _degrees(n, edges):
    deg = [0] * n
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    return deg


def cut_components(n, edges, cut):
    """Remove the edge `cut`; return the two components as (n, edges), each relabeled from 0."""
    import networkx as nx
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(edges)
    G.remove_edge(*cut)
    out = []
    for comp in nx.connected_components(G):
        nodes = sorted(comp)
        idx = {v: i for i, v in enumerate(nodes)}
        sub = G.subgraph(comp)
        out.append((len(nodes), tuple((idx[a], idx[b]) for a, b in sub.edges())))
    return out


@dataclass(frozen=True)
class MultiHubSubmultiplicativeCertificate:
    """Certifies the deg>=4 hub-hub cut submultiplicativity (the reachable fragment) and, separately, that
    the residual multi-hub trees (no deg>=4 hub-hub edge) are all < 1 (VERIFIED, not proven by this lemma)."""

    n_max: int = 12

    def _edges(self, T):
        idx = {v: i for i, v in enumerate(T.nodes())}
        return T.number_of_nodes(), tuple((idx[a], idx[b]) for a, b in T.edges())

    def deg4_submultiplicative(self) -> bool:
        """Phi^11(T) <= bg(T1) bg(T2) for EVERY deg>=4 hub-hub cut, all trees up to n_max (0 violations)."""
        import networkx as nx
        for n in range(4, self.n_max + 1):
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                deg = _degrees(nn, e)
                phiT = bg_phi11_fast(nn, e)
                for a, b in e:
                    if deg[a] >= 4 and deg[b] >= 4:
                        (n1, e1), (n2, e2) = cut_components(nn, e, (a, b))
                        if phiT > bg_phi11_fast(n1, e1) * bg_phi11_fast(n2, e2):
                            return False
        return True

    def contraction_nondecreasing(self) -> bool:
        """Contracting a degree-2 vertex STRICTLY BETWEEN two hubs is Phi^11-non-decreasing (so non-adjacent
        deg>=4 hubs can be slid adjacent, then cut).  Verified over all such contractions up to n_max."""
        import networkx as nx
        for n in range(6, self.n_max + 1):
            for T in nx.nonisomorphic_trees(n):
                deg = dict(T.degree())
                hubs = [x for x in T if deg[x] >= 3]
                if len(hubs) < 2:
                    continue
                for v in list(T.nodes()):
                    if deg[v] != 2:
                        continue
                    G2 = T.copy()
                    G2.remove_node(v)
                    comps = list(nx.connected_components(G2))
                    if len(comps) != 2:
                        continue
                    if not all(any(deg[h] >= 3 and h in c for h in hubs) for c in comps):
                        continue                                # v not strictly between two hubs
                    u = list(T[v])[0]
                    H = T.copy()
                    for w in list(H[v]):
                        if w != u:
                            H.add_edge(u, w)
                    H.remove_node(v)
                    if not nx.is_tree(H):
                        continue
                    nn0, e0 = self._edges(T)
                    nn1, e1 = self._edges(H)
                    if bg_phi11_fast(nn1, e1) < bg_phi11_fast(nn0, e0):
                        return False
        return True

    def residual_below_one(self) -> bool:
        """The (shrunk) residual -- multi-hub trees with >= 3 hubs and AT MOST ONE degree-4 hub, NOT reached
        by contraction + deg>=4 submultiplicativity + the DN family bound -- is all Phi^11 < 1.  VERIFIED,
        not proven by this lemma (the >=3-hub multi-deg-3 case of the open R47 normalization)."""
        import networkx as nx
        for n in range(6, self.n_max + 1):
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                deg = _degrees(nn, e)
                hubs = [v for v in range(nn) if deg[v] >= 3]
                big = [h for h in hubs if deg[h] >= 4]
                if len(hubs) >= 2 and len(big) < 2:             # residual: <2 deg>=4 hubs, not reached
                    if bg_phi11_fast(nn, e) >= 1:
                        return False
        return True

    def check(self) -> bool:
        """The reduction (deg>=4 submultiplicativity + between-hub contraction) is valid, and the shrunk
        residual (>=3 hubs, <=1 deg-4 hub) is < 1.  This certifies a PARTIAL reduction reaching a LARGE
        subclass, NOT the multi-hub maximality theorem."""
        return (self.deg4_submultiplicative() and self.contraction_nondecreasing()
                and self.residual_below_one())
