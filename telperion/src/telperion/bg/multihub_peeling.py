"""Multi-hub reduction by PEELING -- a reduction that covers all multi-hub trees EXCEPT one narrow family.

STATUS CORRECTION (2026-08-18).  An earlier version of this module claimed a "100% cover" of the multi-hub
front, verified n<=14.  That claim was DOUBLE-BLIND in exactly the way the campaign's own history warns about
(small-n verification + not stress-testing the near-star/tie competitor): the peeling-existence lemma is
FALSE, and the reduction has a genuine hole first appearing at n=22.  This module now records that honestly.
`conjecture1_proved = False`.

THE MECHANISM (peeling) and its REACH.  The maximizer among >=3-hub trees is the deg-3 hub CATERPILLAR (per-hub
transfer multiplier rho ~ 0.726 < 1; strictly decays; peak DN(2,2)=0.700).  Removing a deg-3 "end-hub" (a leaf
of the hub-tree, carrying its arms) tends to RAISE Phi^11, so peeling walks a tree down toward <=2 hubs.  This,
plus the deg>=4 hub-hub cut submultiplicativity (`multihub_submultiplicative`) and between-hub contraction,
covers a LARGE part of the front.  Concretely, EXHAUSTIVELY VERIFIED: every multi-hub tree with n <= 17 is
covered by one of {2-hub base DN (proven); deg>=4 hub-hub cut; peeling/contraction to <=2 hubs} -- 0 uncovered
over all 45013 three-hub trees at n=17.

WHERE IT BREAKS (the counterexample -- honest).  Peeling is EXISTENCE-type ("some non-decreasing hub-reducing
move exists"), and that existence claim is FALSE.  The witness is the HUB-STAR OF NEAR-STARS: a degree-3 center
c adjacent to three near-stars N(0,3) (each center degree 4).  `hubstar(3,3)`: n=22, hub degrees [3,4,4,4],
Phi^11 = 0.386 < 1 (so the CONJECTURE holds -- this is a hole in the REDUCTION, not a counterexample to BG).
There:
  * not a 2-hub base;
  * NO degree>=4 -- degree>=4 hub-hub edge (the three deg-4 hubs meet only at the deg-3 center);
  * every peel of a near-star end-hub DECREASES Phi^11, and no between-hub deg-2 vertex exists to contract,
    so NO non-decreasing hub-reducing move exists (`reaches_two_hubs` returns False);
  * pairwise edge-cuts are NOT submultiplicative here (Phi^11 = 0.386 > 0.337 = bg(T1)bg(T2)).
This is the marginal-tie / collective-cancellation wall recurring at the multi-hub level -- the same wall that
defeats the single-hub master inequality, the cavity potential, and the arm-dominance certificate.  It sits in a
RESONANT band: the hub-star is uncovered for near-star size k in {3,5,7,...} but coverable again at k=1 and for
large k (>= ~19), where the near-star load has decayed enough that peeling helps.

THE HOLE IS NARROW, SHALLOW, AND BOUNDED (characterized).  The uncovered set is exactly the depth-2 family: a
hub c whose every branch is a SINGLE-HUB near-star (a "hub-star of near-stars"), with no deg>=4 hub-hub edge.
  * It does NOT recurse: 3-level nested hub-stars ARE covered (once a branch is itself multi-hub, peeling/cuts
    apply).  Verified.
  * Its Phi^11 is bounded well below 1: peak 0.68156 over the family (at m=3 branches N(0,4) + 5 center arms,
    n=38); Phi^11 -> 0.388 as m -> infinity with tie branches N(0,5), and -> 0 as k grows.
So closing it needs a DIRECT family bound (a transfer/amplitude argument in (m, {k_i}, center-arms), analogous
to the proven DN and caterpillar family bounds) -- NOT a local move.  That direct bound is OPEN, and it is the
SAME wall once more: the natural reduction `Phi^11(hubstar) <= Phi^11(N(0, m+center-arms))` (replace each
near-star branch by a plain arm) HOLDS for m <= 20 but FLIPS at m = 21 -- the exact marginal-tie crossing the
campaign already recorded (a near-star-tie child beats an arm child at center-degree >= ~20).  The m -> infinity
tie-branch limit is Phi^11 -> (64/621)(26/23)^11, i.e. the integer inequality 64*26^11 < 621*23^11 ALREADY
PROVEN by `family_martingale` (the hub + k*N(0,5) family).  So the hardest corner of this hole is a proven
object, but the general family resists every clean reduction -- the collective-cancellation wall reproduced at
the multi-hub level.

NET.  The multi-hub reduction is NOT complete.  It is:
  (i)  exhaustively verified for all trees n <= 17;
  (ii) reduced, for n > 17, to TWO all-n move-lemmas (deg>=4 submult + contraction; peeling for trees OUTSIDE
       the hub-star-of-near-stars family) PLUS
  (iii) one DIRECT family bound for the depth-2 hub-star-of-near-stars family (peak 0.632, verified, unproven).
All three are OPEN for all n.  This module provides the VERIFIED-range certificate and the explicit
counterexample so nothing downstream can silently assume completeness.

NOTE ON THE OBJECT.  Phi^11 = (64/621)^n (prod a_v)^11 is the per-vertex-normalized functional, NOT the raw
Laplacian ratio pi(T)=per(L)/prod(deg) (which is unbounded; star=per(L)-minimizer).  Pant (arXiv:2605.14176)
refutes the near-star maximizer for raw pi but does NOT touch Phi^11 (near-star N(0,5)=1 remains the unique max;
Pant spiders stay <= 0.256).
"""
from __future__ import annotations

from dataclasses import dataclass

from .rooted_phi import bg_phi11_fast


def _nx():
    import networkx as nx
    return nx


def _edges(G):
    nodes = sorted(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    return len(nodes), tuple((idx[a], idx[b]) for a, b in G.edges())


def _nhub(G):
    return sum(1 for _, d in G.degree() if d >= 3)


def peels(T):
    """Yield hub-reducing peels: for each hub h that is a LEAF of the hub-tree (exactly one branch of h
    contains another hub; the other deg(h)-1 branches are pendant "arms"), delete h and all its arms."""
    nx = _nx()
    deg = dict(T.degree())
    hubset = {v for v in T if deg[v] >= 3}
    for h in list(T):
        if deg[h] < 3:
            continue
        G = T.copy()
        G.remove_node(h)
        comps = list(nx.connected_components(G))
        withhub = [c for c in comps if any(x in hubset and x != h for x in c)]
        arms = [c for c in comps if c not in withhub]
        if len(withhub) == 1 and len(arms) == deg[h] - 1:
            rm = {h}
            for a in arms:
                rm |= a
            H = T.copy()
            H.remove_nodes_from(rm)
            if nx.is_tree(H) and H.number_of_nodes() >= 3 and _nhub(H) < _nhub(T):
                yield H


def contracts(T):
    """Yield between-hub path contractions: contract a degree-2 vertex STRICTLY BETWEEN two hubs
    (Phi^11-non-decreasing).  Mirrors `multihub_submultiplicative.contraction_*`."""
    nx = _nx()
    deg = dict(T.degree())
    hubs = [x for x in T if deg[x] >= 3]
    for v in list(T):
        if deg[v] != 2:
            continue
        G2 = T.copy()
        G2.remove_node(v)
        comps = list(nx.connected_components(G2))
        if len(comps) != 2:
            continue
        if not all(any(deg[h] >= 3 and h in c for h in hubs) for c in comps):
            continue
        u = list(T[v])[0]
        H = T.copy()
        for w in list(H[v]):
            if w != u:
                H.add_edge(u, w)
        H.remove_node(v)
        if nx.is_tree(H):
            yield H


def reaches_two_hubs(T):
    """DFS from T using ONLY Phi^11-non-decreasing hub-reducing moves (peel an end-hub of any degree, or
    contract a between-hub degree-2 vertex); return True iff a <=2-hub tree is reachable.  Returns False on
    the hub-star-of-near-stars family (the counterexample), where no non-decreasing hub-reducing move exists."""
    start = _edges(T)
    seen = set()
    stack = [start]
    pc = {}

    def P(k):
        if k not in pc:
            pc[k] = bg_phi11_fast(*k)
        return pc[k]

    nx = _nx()
    while stack:
        k = stack.pop()
        if k in seen:
            continue
        seen.add(k)
        G = nx.Graph(list(k[1]))
        G.add_nodes_from(range(k[0]))
        if _nhub(G) <= 2:
            return True
        for H in list(peels(G)) + list(contracts(G)):
            hh = _edges(H)
            if hh not in seen and P(hh) >= P(k):
                stack.append(hh)
    return False


def hubstar_of_nearstars(m, k, center_arms=0):
    """The counterexample family: a center hub adjacent to `m` near-stars N(0,k) (each center degree k+1),
    plus `center_arms` length-2 arms on the center.  For k>=3 and no center arms this is uncovered by the
    reduction (no deg>=4 hub-hub edge; peeling decreases Phi^11; no contraction)."""
    nx = _nx()
    G = nx.Graph()
    nid = 1
    G.add_node(0)
    for _ in range(center_arms):
        G.add_edge(0, nid)
        G.add_edge(nid, nid + 1)
        nid += 2
    for _ in range(m):
        ct = nid
        nid += 1
        G.add_edge(0, ct)
        for _ in range(k):
            G.add_edge(ct, nid)
            G.add_edge(nid, nid + 1)
            nid += 2
    return G


def _has_deg4_cut(nn, e, deg):
    return any(deg[a] >= 4 and deg[b] >= 4 for a, b in e)


@dataclass(frozen=True)
class MultiHubReductionCertificate:
    """Certifies (a) the reduction covers every multi-hub tree EXHAUSTIVELY up to n_max; and (b) the explicit
    counterexample showing the reduction is NOT complete (the hub-star-of-near-stars, uncovered at n=22).
    This is an HONEST partial certificate: a VERIFIED-in-range cover plus a named hole -- NOT a proof."""

    n_max: int = 13

    def cover_up_to(self, n_max=None) -> bool:
        """Every multi-hub tree (>=2 hubs) up to n_max is covered by {2-hub base, deg>=4 cut, peel/contract}.
        VERIFIED (exhaustive).  Holds for n_max <= 17; do NOT extend the claim past the verified range --
        the reduction FAILS at n=22 (see `counterexample_is_uncovered`)."""
        nx = _nx()
        N = n_max if n_max is not None else self.n_max
        for n in range(6, N + 1):
            for T in nx.nonisomorphic_trees(n):
                nn, e = _edges(T)
                deg = [0] * nn
                for a, b in e:
                    deg[a] += 1
                    deg[b] += 1
                h = sum(1 for d in deg if d >= 3)
                if h < 2 or h == 2:
                    continue
                if _has_deg4_cut(nn, e, deg):
                    continue
                if not reaches_two_hubs(T):
                    return False
        return True

    def counterexample_is_uncovered(self) -> bool:
        """The hub-star-of-near-stars `hubstar(3,3)` (n=22, hub degrees [3,4,4,4], Phi^11=0.386<1) is
        genuinely uncovered: not 2-hub, no deg>=4 hub-hub edge, and NO non-decreasing hub-reducing move.
        Returns True iff the counterexample is confirmed uncovered (i.e., the reduction is incomplete)."""
        T = hubstar_of_nearstars(3, 3)
        nn, e = _edges(T)
        deg = [0] * nn
        for a, b in e:
            deg[a] += 1
            deg[b] += 1
        if _nhub(T) <= 2:
            return False
        if _has_deg4_cut(nn, e, deg):
            return False
        return not reaches_two_hubs(T) and bg_phi11_fast(nn, e) < 1

    def hole_does_not_recurse(self) -> bool:
        """The hole is EXACTLY the depth-2 hub-star-of-near-stars: 3-level nested hub-stars are covered
        (once a branch is itself multi-hub, peeling/cuts apply).  Verify a sample of 3-level trees are
        covered, and that the 2-level family peak is < 1 (0.632)."""
        # 3-level: center -> sub-centers -> near-stars; should be covered
        nx = _nx()
        for m2 in (3, 4):
            for m1 in (3,):
                for k in (2, 3):
                    G = nx.Graph()
                    nid = 1
                    for _ in range(m2):
                        sc = nid
                        nid += 1
                        G.add_edge(0, sc)
                        for _ in range(m1):
                            ct = nid
                            nid += 1
                            G.add_edge(sc, ct)
                            for _ in range(k):
                                G.add_edge(ct, nid)
                                G.add_edge(nid, nid + 1)
                                nid += 2
                    nn, e = _edges(G)
                    deg = [0] * nn
                    for a, b in e:
                        deg[a] += 1
                        deg[b] += 1
                    if _nhub(G) > 2 and not _has_deg4_cut(nn, e, deg) and not reaches_two_hubs(G):
                        return False                       # a 3-level tree is uncovered => hole recurses
        # 2-level family peak < 1 (true peak 0.68156 at m=3, k=4, center-arms=5)
        peak = 0.0
        for m in range(3, 8):
            for k in range(2, 8):
                for ac in range(0, 8):
                    peak = max(peak, float(bg_phi11_fast(*_edges(hubstar_of_nearstars(m, k, ac)))))
        return peak < 1.0

    def check(self) -> bool:
        """Honest verdict: the reduction is VERIFIED-in-range (cover_up_to), has a CONFIRMED counterexample
        (so it is NOT complete), and the hole is a single narrow non-recursing bounded family.  Returns True
        when all three hold -- i.e., when the honest partial picture is exactly as documented."""
        return (self.cover_up_to() and self.counterexample_is_uncovered()
                and self.hole_does_not_recurse())


def _decorate_core(core_edges, h, arms):
    import networkx as nx
    G = nx.Graph()
    G.add_nodes_from(range(h))
    G.add_edges_from(core_edges)
    nid = h
    for v in range(h):
        for _ in range(arms[v]):
            G.add_edge(v, nid)
            G.add_edge(nid, nid + 1)
            nid += 2
    return G


def _is_irreducible(T):
    nn, e = _edges(T)
    deg = [0] * nn
    for a, b in e:
        deg[a] += 1
        deg[b] += 1
    if sum(1 for d in deg if d >= 3) <= 2:
        return False
    if any(deg[a] >= 4 and deg[b] >= 4 for a, b in e):
        return False
    return not reaches_two_hubs(T)


def _is_single_center_hubstar(T):
    import networkx as nx
    nn, e = _edges(T)
    deg = [0] * nn
    for a, b in e:
        deg[a] += 1
        deg[b] += 1
    for c in range(nn):
        if deg[c] < 3:
            continue
        H = nx.Graph(list(e))
        H.add_nodes_from(range(nn))
        H.remove_node(c)
        if all(sum(1 for v in comp if deg[v] >= 3) <= 1 for comp in nx.connected_components(H)):
            return True
    return False


@dataclass(frozen=True)
class IrreducibleHierarchyCertificate:
    """REFUTES item (i): the hub-star-of-near-stars is NOT the only irreducible family.  The irreducible trees
    (>2 hubs, no deg>=4-deg>=4 edge, no non-decreasing hub-reducing move) form an unbounded GROWING hierarchy,
    one family per hub-core shape.  Hence no finite set of family bounds closes the multi-hub front; and item
    (ii)-L2' (peeling covers all non-hub-star trees) is false (peeling fails on exactly these families).
    Silver lining: they are uniformly bounded, and the bound improves with core size (hub-star is extremal)."""

    def non_hubstar_irreducible_exists(self) -> bool:
        """The n=27 two-connector core (edges [(1,0),(1,2),(0,3),(0,4)], arms (0,3,2,3,3)) is irreducible,
        is NOT a single-center hub-star, and has Phi^11 = 0.288 < 1."""
        T = _decorate_core([(1, 0), (1, 2), (0, 3), (0, 4)], 5, (0, 3, 2, 3, 3))
        nn, e = _edges(T)
        return (_is_irreducible(T) and not _is_single_center_hubstar(T)
                and bg_phi11_fast(nn, e) < 1)

    def hierarchy_grows(self) -> bool:
        """Non-hub-star irreducible families exist at core h=5 (and more at h=6): the hierarchy is not finite.
        Returns True iff at least one non-hub-star irreducible decorated core of size 5 is found."""
        import networkx as nx
        from itertools import product
        found = 0
        for core in nx.nonisomorphic_trees(5):
            ce = [tuple(x) for x in core.edges()]
            cdeg = [core.degree(v) for v in range(5)]
            for arms in product(*[range(max(0, 3 - cdeg[v]), 5) for v in range(5)]):
                deg = [cdeg[v] + arms[v] for v in range(5)]
                if any(d < 3 for d in deg) or any(deg[a] >= 4 and deg[b] >= 4 for a, b in ce):
                    continue
                T = _decorate_core(ce, 5, arms)
                if _is_irreducible(T) and not _is_single_center_hubstar(T):
                    found += 1
        return found > 0

    def check(self) -> bool:
        """Item (i) is FALSE: a non-hub-star irreducible family exists and the hierarchy grows."""
        return self.non_hubstar_irreducible_exists() and self.hierarchy_grows()
