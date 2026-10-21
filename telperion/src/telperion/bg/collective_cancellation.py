"""Structure of the collective-cancellation crux -- honest STRUCTURAL observations, NOT a proof.

The open half of Brualdi-Goldwasser is `Φ¹¹(T) ≤ 1` for all trees.  Writing `Φ¹¹ = ∏_v b_v` with the
per-vertex benchmarked factor

    b_v := (64/621) · a_v¹¹,     a_v = 1 + z_v S_v  (the rational cavity amplitude),

the difficulty is that the `b_v` are NOT individually ≤ 1: at the tie they are `{0.103 (leaf),
8.914 (mid), 1.528 (hub)}` and `∏ = 1` only by a COLLECTIVE cancellation (the councils proved no
per-vertex/sum-of-non-positive-terms argument can work).  This module records two honest, correctly-scoped
observations that sharpen the picture -- neither closes the `≤` half.

OBSERVATION 1 (per-root reduction, a methodological fact).  `Φ¹¹(T) = max_root Φ¹¹(T,r) ≤ 1` iff
`Φ¹¹(T,r) ≤ 1` for EVERY root r (verified all roots, all trees n ≤ 10).  So a proof may fix an arbitrary
root and use the bottom-up cavity, never needing to identify the maximizing root.

OBSERVATION 2 (the arm-vs-hub balance).  Grouping a length-2 arm (mid + leaf) gives
`b_mid · b_leaf = (64/621)²(3/2)¹¹ = D∞² = 0.918715 < 1` -- a sub-unit block.  A hub of degree k carries
the excess `b_hub(k) = (64/621)((4k+3)/(3(k+1)))¹¹ > 1`.  The near-star `Φ¹¹(N(0,k)) = b_hub(k) · (arm)^k`
is the product of the excess hub and k sub-unit arms; it is maximized at the INTEGER k = 5 (`= 1`, the tie)
and `< 1` for every other k (0.9888 at k=4, 0.9835 at k=6).  So the tie is exactly where a degree-5 hub's
excess is balanced by five sub-unit arms.

HONEST SCOPE.  These are STRUCTURAL descriptions.  The `≤` half itself remains OPEN: the collective
inductive step -- that `b_v · ∏(child products) ≤ 1` given the children `≤ 1` -- does NOT follow, because
`b_v > 1` is possible and the compensation requires bounding the child CAVITIES `m_c`, which is exactly the
cavity-potential problem that stalls (residual `+0.199` at the tie; no finite-basis potential closes it).
This module proves nothing new about the conjecture.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def per_vertex_factor(a):
    """b_v = (64/621) · a¹¹ -- the benchmarked per-vertex factor (Φ¹¹ = ∏_v b_v).  `a` a Fraction."""
    return Fr(64, 621) * a ** 11


def arm_factor():
    """The length-2 arm (mid a=3/2, leaf a=1) benchmarked block: b_mid·b_leaf = (64/621)²(3/2)¹¹ = D∞² < 1."""
    return per_vertex_factor(Fr(3, 2)) * per_vertex_factor(Fr(1))


def hub_factor(k):
    """The excess factor of a degree-k legs-2 hub: b(a_hub), a_hub = (4k+3)/(3(k+1)).  > 1 for the tie hub."""
    return per_vertex_factor(Fr(4 * k + 3, 3 * (k + 1)))


def near_star_balance(k):
    """Φ¹¹(N(0,k)) = hub_factor(k) · arm_factor()^k -- the excess hub balanced by k sub-unit arms."""
    return hub_factor(k) * arm_factor() ** k


@dataclass(frozen=True)
class CollectiveCancellationNote:
    """Certifies the two structural observations (per-root reduction; arm-vs-hub balance) -- explicitly a
    description of the crux's structure, NOT a proof of the `≤` half."""

    n_max: int = 10

    def _edges(self, T):
        idx = {v: i for i, v in enumerate(T.nodes())}
        return T.number_of_nodes(), tuple((idx[a], idx[b]) for a, b in T.edges())

    def per_root_bound(self) -> bool:
        """Φ¹¹(T,r) ≤ 1 for EVERY root of every tree up to n_max (the per-root reduction)."""
        import networkx as nx

        from .rooted_phi import phi11_rooted
        for n in range(3, self.n_max + 1):
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                for r in range(nn):
                    if phi11_rooted(nn, e, r) > 1:
                        return False
        return True

    def arm_is_subunit(self) -> bool:
        """The length-2 arm block is strictly below 1 (= D∞²)."""
        return arm_factor() < 1

    def tie_is_the_balance(self) -> bool:
        """near_star_balance(k) = Φ¹¹(N(0,k)) is maximized at the integer k = 5 (= 1), < 1 elsewhere."""
        vals = {k: near_star_balance(k) for k in range(0, 30)}
        return vals[5] == 1 and all(vals[k] < 1 for k in vals if k != 5)

    def check(self) -> bool:
        return self.per_root_bound() and self.arm_is_subunit() and self.tie_is_the_balance()
