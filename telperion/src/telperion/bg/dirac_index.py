"""Probe (physics transfer #2): the discrete Dirac operator's index and the Brualdi-Goldwasser tie / 11|n gate.

The Atiyah-Singer index theorem is the archetype "a continuous-looking analytic quantity is forced to be a
topological INTEGER."  A tree is bipartite, so its adjacency carries a natural chirality (the bipartite +-1
grading = `gamma^5`), and `D + iA` is a discrete Dirac operator.  Its chiral index -- the imbalance of the
two colour classes, `ind = |X| - |Y|` (equal to the adjacency nullity `n - 2*nu` for a tree) -- is an integer
that changes only in integer steps, so it CANNOT overshoot between integer arm-counts.  This probe asks
whether that index jumps at the tie / encodes the `11 | n` gate (a tie forces `11 | n`, `sporadic_tie.py`).

FINDING (NEGATIVE; the index is the WRONG integer, and the probe shows exactly why).
On near-stars the chiral index is `+1` for EVERY `s` (`|X|-|Y| = (1+s) - s = 1`; nullity `= 1`), constant --
it does not move at the tie.  Across all trees the index ranges over the parity interval `[-(n-2), n-2]`,
entirely UNRELATED to `n mod 11`.  Meanwhile the 23-adic defect `delta = v_23(Phi^11)` (`resonance_carrier.py`)
IS `0` exactly at the tie and `!= 0` off it -- it is the integer that localizes the tie, and it forces `11|n`.
So there ARE integers that localize the tie (the arithmetic `delta`), and there are integers that are robust
under deformation (the Dirac index), but they are DIFFERENT integers: the Dirac index is spectral/topological
(a parity / bipartite imbalance), while the tie's resonance is 23-adic (the amplitude product's valuation).

WHY (the unified conclusion of the three physics probes).  The index theorem gives the right PRINCIPLE --
"analytic = integer, no overshoot" -- but the tree's Dirac index is a GEOMETRIC integer and the tie is an
ARITHMETIC one.  An archimedean/geometric index cannot see the `(64/621)^n` arithmetic balance that defines
the tie; only the 23-adic carrier does.  Together with `susy_index.py` (Witten index) and
`determinantal_kernel.py` (free-fermion determinant), this pins the lesson: physics supplies non-separable,
deformation-invariant integers of the right SHAPE, but the certifying integer for BG is arithmetic, not
spectral.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass


def bipartition(n, edges):
    """The two colour classes `(X, Y)` of the (bipartite) tree, as vertex-index sets."""
    g = {i: [] for i in range(n)}
    for a, b in edges:
        g[a].append(b)
        g[b].append(a)
    color = {0: 0}
    stack = [0]
    while stack:
        v = stack.pop()
        for w in g[v]:
            if w not in color:
                color[w] = 1 - color[v]
                stack.append(w)
    X = {v for v, c in color.items() if c == 0}
    Y = {v for v, c in color.items() if c == 1}
    return X, Y


def dirac_chiral_index(n, edges) -> int:
    """The discrete chiral Dirac index `|X| - |Y|` (bipartite imbalance) -- an integer topological index that
    equals the adjacency nullity `n - 2*nu` for a tree."""
    X, Y = bipartition(n, edges)
    return len(X) - len(Y)


def adjacency_nullity(n, edges) -> int:
    import numpy as np
    A = np.zeros((n, n))
    for a, b in edges:
        A[a, b] = 1
        A[b, a] = 1
    return int(sum(1 for v in np.linalg.eigvalsh(A) if abs(v) < 1e-9))


@dataclass(frozen=True)
class DiracIndexProbe:
    """Physics-transfer probe #2: does the tree's discrete Dirac index localize the tie / the 11|n gate?
    Verifies the index is an integer topological invariant that equals the nullity but is constant on
    near-stars and unrelated to `n mod 11`, while the 23-adic defect DOES localize the tie.  `check()`
    certifies this contrast, NOT BG."""

    near_star_s: tuple = (2, 3, 4, 5, 6)
    gate_ns: tuple = (7, 8, 9, 10, 11, 12)

    def index_equals_nullity_on_near_stars(self) -> bool:
        """`|X|-|Y| = nullity(A) = 1` for every near-star -- an integer topological index (right shape)."""
        from .frustration_free import near_star_edges
        for s in self.near_star_s:
            n, e = near_star_edges(s)
            if not (dirac_chiral_index(n, e) == adjacency_nullity(n, e) == 1):
                return False
        return True

    def index_does_not_localize_tie(self) -> bool:
        """The Dirac index is constant (`+1`) across the whole near-star family -- it does not move at the
        tie."""
        from .frustration_free import near_star_edges
        return len({dirac_chiral_index(*near_star_edges(s)) for s in self.near_star_s}) == 1

    def gate_is_23adic_not_dirac(self) -> bool:
        """The 23-adic defect localizes the tie (`delta = 0` at N(0,5), `!= 0` off it) while the Dirac index
        does not; and across trees the Dirac index is unrelated to `n mod 11`."""
        import networkx as nx
        from .frustration_free import near_star_edges
        from .resonance_carrier import phi11_23adic_valuation
        # 23-adic delta localizes the tie; Dirac index (=+1) does not
        n5, e5 = near_star_edges(5)
        if phi11_23adic_valuation(n5, e5) != 0 or dirac_chiral_index(n5, e5) != 1:
            return False
        n4, e4 = near_star_edges(4)
        if phi11_23adic_valuation(n4, e4) == 0:      # off-tie: 23-adic delta != 0 (localizes)
            return False
        if dirac_chiral_index(n4, e4) != 1:          # ...but the Dirac index is the same +1 (does not)
            return False
        # the index varies widely across trees with no n-mod-11 structure (all same parity as n; the tie's
        # +1 is just one shared value) -- unlike the 23-adic delta which is pinned to the tie
        for N in self.gate_ns:
            idxs = set()
            for T in nx.nonisomorphic_trees(N):
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                idxs.add(dirac_chiral_index(N, e))
            if len(idxs) < 3:                             # index varies (not a tie-localizing signal)
                return False
            if any((v - N) % 2 != 0 for v in idxs):       # every index has the parity of n (n = |X|+|Y|)
                return False
        return True

    def finding(self) -> str:
        return (
            "NEGATIVE; the Dirac index is the WRONG integer, and the probe shows why. The discrete chiral "
            "Dirac index |X|-|Y| (= adjacency nullity n-2nu for a tree) is a genuine integer topological "
            "invariant -- deformation-invariant, so it cannot overshoot -- but it is CONSTANT (+1) on the "
            "whole near-star family and, across trees, ranges over the parity interval [-(n-2), n-2] "
            "UNRELATED to n mod 11. It does not jump at the tie or encode the 11|n gate. The 23-adic defect "
            "delta = v_23(Phi^11), by contrast, IS 0 exactly at the tie and != 0 off it, and forces 11|n. So "
            "the index theorem gives the right PRINCIPLE (analytic = integer, no overshoot) but the tree's "
            "Dirac index is a GEOMETRIC integer while the tie is an ARITHMETIC one -- an archimedean index "
            "cannot see the (64/621)^n balance. With the SUSY (Witten) and determinantal probes, the lesson "
            "is unified: physics supplies deformation-invariant integers of the right shape, but BG's "
            "certifying integer is 23-adic, not spectral. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies: the Dirac index is the integer nullity (right shape), is constant on near-stars (does
        not localize the tie), and the tie/11|n gate is 23-adic not Dirac -- NOT BG."""
        return (
            self.index_equals_nullity_on_near_stars()
            and self.index_does_not_localize_tie()
            and self.gate_is_23adic_not_dirac()
        )
