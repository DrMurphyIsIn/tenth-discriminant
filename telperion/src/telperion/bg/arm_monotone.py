"""R1 -- arithmetic single-hub closure via message-vs-Phi^11 monotonicity.

Target (from `arm_maximal.py`): the arm maximizes `F_B = Phi^11_rooted(B)` among large-message blocks, i.e.
`F_B <= 486/529`.  This module attacks it INDUCTIVELY (assuming `F_child <= 1`, BG for smaller trees) via the
message-vs-`Phi^11` MONOTONICITY, and closes two of the three structural cases, isolating the residual.

THE MONOTONICITY.  For a `j = 1` block with child `c`, `F_B = (64/621)(1 + mu_c/2)^11 F_c` is INCREASING in
the child message `mu_c` (for fixed `F_c`).  Chaining a link (mid-extension) multiplies `F` by
`(64/621)(1 + mu/2)^11`, which is `< 1` for every chain message `mu >= 1/3` (a contraction).

CASE 1 -- CHAINS (proved).  Among all rooted PATHS `P_m`, `F` is maximized by `P_2` = the ARM (`F = 486/529`):
`F(P_1) = 64/621`, `F(P_2) = 486/529`, and each further link contracts (`F(P_3) = 1977326743/...`, factor
`~0.56`, then `~0.82` each), so `F(P_m) < F(P_2)` for `m >= 3`.  The arm is the unique path maximizer.

CASE 2 -- LEAF-CHILD BLOCKS (proved, inductively).  If a block has a LEAF child, the arm-maximal bound
follows from `F <= 1` on the OTHER children.  `j = 1` leaf child IS the arm (equality).  `j = 2` with one leaf
child: `F_B = (64/621)^2 ((4+mu_2)/3)^11 F_{c2}` with `mu_2 < 0.357` (large-message), and the required
`F_{c2} <= [9/(2(4+mu_2))]^11 >= (9/8.71)^11 = 1.44 >= 1` holds since `F_{c2} <= 1`.  Verified on the census.

THE RESIDUAL (the branching obstruction).  What remains is `j >= 2` blocks with ALL children NON-leaf.  There
the crude `F_child <= 1` is too weak (it gives `F_B <= (64/621) a_B^11 ~ 6.4 > 486/529`) and the tighter
master bound reintroduces the `C^{j-1}` blowup -- the collective cancellation.  So the arithmetic monotonicity
closes chains and leaf-child blocks; the all-non-leaf-branching residual reduces to the master inequality of
`arm_maximal.py`.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .mixed_block_martingale import block_amplitude_and_message, block_factor

RHO_B_11 = Fr(621, 64)
F_ARM = Fr(486, 529)


def chain_link_factor(mu: Fr) -> Fr:
    """The per-link chain (mid-extension) multiplier on `F`: `(64/621)(1 + mu/2)^11`.  `< 1` for chain
    messages `mu >= 1/3` (a contraction)."""
    return Fr(64, 621) * (1 + mu / 2) ** 11


def rooted_path(m: int):
    """The rooted path `P_m` (root at one end): `m` vertices, chain to a leaf."""
    return m, tuple((i, i + 1) for i in range(m - 1)), 0


def path_F(m: int) -> Fr:
    """`F = Phi^11_rooted(P_m)` for the rooted path."""
    n, e, r = rooted_path(m)
    return block_factor(n, e, r)


def _has_leaf_child(n, edges, root) -> bool:
    g = {i: set() for i in range(n)}
    for a, b in edges:
        g[a].add(b)
        g[b].add(a)
    for c in g[root]:
        if len(g[c]) == 1:          # child of the root with degree 1 = a leaf child
            return True
    return False


@dataclass(frozen=True)
class ArmMonotoneCertificate:
    """R1: arithmetic single-hub closure via message-vs-Phi^11 monotonicity.  `check()` certifies the chain
    contraction (arm maximal among paths), the leaf-child reduction (bounded via F_child <= 1), and isolates
    the all-non-leaf-branching residual -- a partial closure of the arm-maximal, NOT the full master
    inequality, NOT BG.  conjecture1_proved = False."""

    census_m: int = 8
    path_check: int = 8

    def chain_contraction_holds(self) -> bool:
        """Each chain link contracts: `chain_link_factor(mu) < 1` for chain messages, and `F(P_m)` is
        decreasing for `m >= 2` -- so the arm `P_2` maximizes `F` among rooted paths."""
        for mu in (Fr(1, 3), Fr(3, 7), Fr(7, 17), Fr(17, 41), Fr(41, 99)):
            if not chain_link_factor(mu) < 1:
                return False
        return all(path_F(m + 1) < path_F(m) for m in range(2, self.path_check))

    def arm_is_max_path(self) -> bool:
        """`F(P_2) = 486/529` is the maximum of `F` over all rooted paths (the arm is the path maximizer)."""
        return path_F(2) == F_ARM and all(path_F(m) < F_ARM for m in range(3, self.path_check + 1))

    def leaf_child_blocks_bounded(self) -> bool:
        """Every large-message block WITH a leaf child has `F_B <= 486/529` (via the monotonicity plus
        `F_other <= 1`).  Verified on the census; the arm attains equality."""
        import networkx as nx
        arm_hit = False
        for m in range(1, self.census_m + 1):
            trees = [nx.empty_graph(1)] if m == 1 else list(nx.nonisomorphic_trees(m))
            for T in trees:
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                for r in range(m):
                    _alpha, mu = block_amplitude_and_message(m, e, r)
                    if (1 + mu) ** 11 <= RHO_B_11:
                        continue
                    if m == 1 or _has_leaf_child(m, e, r):
                        F = block_factor(m, e, r)
                        if F > F_ARM:
                            return False
                        if F == F_ARM:
                            arm_hit = True
        return arm_hit

    def residual_is_all_nonleaf_branching(self) -> bool:
        """The residual is exactly `j >= 2` blocks with NO leaf child: such blocks EXIST (so the closure is
        partial), and their bound needs the master inequality, not the crude `F_child <= 1`."""
        import networkx as nx
        for m in range(2, self.census_m + 1):
            for T in nx.nonisomorphic_trees(m):
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                for r in range(m):
                    _alpha, mu = block_amplitude_and_message(m, e, r)
                    if (1 + mu) ** 11 <= RHO_B_11:
                        continue
                    g = {i: set() for i in range(m)}
                    for a, b in e:
                        g[a].add(b)
                        g[b].add(a)
                    if len(g[r]) >= 2 and not _has_leaf_child(m, e, r):
                        return True         # an all-non-leaf-branching residual block exists
        return False

    def finding(self) -> str:
        return (
            "PARTIAL single-hub closure via message-vs-Phi^11 monotonicity. The map F_B = (64/621)(1+mu_c/2)^11 "
            "F_c is increasing in mu_c, and chaining a link contracts F by (64/621)(1+mu/2)^11 < 1 (for chain "
            "messages mu >= 1/3). CLOSED: (1) CHAINS -- the arm P_2 (F=486/529) maximizes F over all rooted "
            "paths, each extra link contracting; (2) LEAF-CHILD blocks -- F_B <= 486/529 follows inductively "
            "from F_other <= 1 (the arm is the equality). RESIDUAL: j>=2 blocks with ALL children non-leaf, "
            "where crude F_child<=1 gives F_B <= (64/621)a_B^11 ~ 6.4 (too weak) and the master bound "
            "reintroduces the C^{j-1} blowup. So monotonicity closes chains + leaf-child blocks and isolates "
            "the all-non-leaf-branching residual = the master inequality (arm_maximal). conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the chain contraction (arm maximal among paths), the leaf-child reduction, and the
        existence of the all-non-leaf-branching residual -- a partial closure, NOT the master inequality."""
        return (
            self.chain_contraction_holds()
            and self.arm_is_max_path()
            and self.leaf_child_blocks_bounded()
            and self.residual_is_all_nonleaf_branching()
        )
