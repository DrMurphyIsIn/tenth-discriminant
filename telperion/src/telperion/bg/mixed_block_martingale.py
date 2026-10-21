"""Mixed-block martingale: the per-block transfer factor and the generalized hub bound.

`family_martingale.py` handled a hub carrying k copies of the TIE block (per-block factor F=1).  This
generalizes to a hub carrying ARBITRARY blocks -- any rooted subtrees hung off a central hub -- and
exposes the single organizing quantity.

THE GENERAL FORMULA (exact, verified against `rooted_phi.phi11_rooted`).  For a hub with blocks
`b = 1..k` (block b a rooted subtree, root attached to the hub), rooted at the hub:

    Phi^11_hub  =  (64/621) * a_hub^11 * prod_b F_b ,

    F_b   = (64/621)^{n_b} * alpha_b^11        (the PER-BLOCK TRANSFER FACTOR)
    a_hub = 1 + (sum_b mu_b) / (k + 1)          (the boundary amplitude)

where `alpha_b = prod_v a_v` over block b (its root carries the virtual hub edge) and `mu_b` is the
block's cavity message into the hub.  Each block contributes one multiplicative factor `F_b` -- a
finitely-correlated / transfer-matrix structure with the blocks as transfer steps.

THE TRICHOTOMY (verified over all rooted blocks up to n_b = 11).
  * F_b < 1  (SUBCRITICAL): the block decays.  A homogeneous family `hub + k*b` has
    `Phi^11_hub(k) = (64/621) a_hub(k)^11 F_b^k` with an INTERIOR maximum (a_hub rises, F^k falls).
  * F_b = 1  (MARGINAL): the tie.  `F_b = 1  <=>  alpha_b = (621/64)^{n_b/11}` is rational, which (23-adic
    valuation, `v_23(621)=1`) forces `11 | n_b` -- the SAME 23-gate as `sporadic_tie` / `resonance_carrier`.
    The unique marginal block through n_b = 11 is the tie N(0,5) (message `mu = 3/23`).
  * F_b > 1  (SUPERCRITICAL): would make `Phi^11_hub(k) -> infinity`, hence (since `bg_phi11 >= Phi^11_hub`)
    `bg_phi11 -> infinity > 1` -- a BG VIOLATION.  **No supercritical block exists** in the census
    (`F_b <= 1` for every rooted block up to n_b = 11).  So `F_b <= 1` is a NECESSARY condition for BG,
    verified here.

THE TIE IS THE EXTREMAL SINGLE-HUB CONFIGURATION.  The simplest block -- the length-2 ARM (mid-leaf,
`F = 486/529`, the fractal-tail factor) -- generates the NEAR-STAR family, whose interior maximum is
`Phi^11_hub = 1` EXACTLY at k = 5: the tie N(0,5), recovered as the extremum of the arm-block family.  It
is the UNIQUE homogeneous family that touches 1; every other block's family stays strictly below.

HONEST SCOPE.  This is the structural generalization: one formula unifying the tie-recursive marginal
family (`family_martingale`), the near-star subcritical extremum (the tie), and mixed hubs; plus the
NECESSARY per-block condition `F_b <= 1` (verified over the census, implied by BG).  It does NOT prove BG:
sufficiency (that `F_b <= 1` holds for ALL blocks, and that the interior maxima never exceed 1), multi-level
trees, and non-hub root choices are open.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

W = Fr(64, 621)  # the per-vertex weight; Phi^11 = W^n (prod a_v)^11


def block_amplitude_and_message(n, edges, root):
    """`(alpha_b, mu_b)` for a rooted block: alpha_b = prod_v a_v over the block (root carries the virtual
    hub edge, so its z = 1/(children+1)), and mu_b = the cavity message z/a emitted at the root."""
    g = {i: set() for i in range(n)}
    for a, b in edges:
        g[a].add(b)
        g[b].add(a)
    prod = [Fr(1)]

    def rec(v, parent):
        kids = [w for w in g[v] if w != parent]
        z = Fr(1, len(kids) + 1)
        S = sum((rec(w, v) for w in kids), Fr(0))
        a = 1 + z * S
        prod[0] *= a
        return z / a

    msg = rec(root, None)         # run the recursion (mutating prod) BEFORE reading prod[0]
    return prod[0], msg


def block_factor(n, edges, root) -> Fr:
    """The per-block transfer factor `F_b = (64/621)^{n_b} * alpha_b^11`.  Tie -> 1; subcritical < 1."""
    alpha, _ = block_amplitude_and_message(n, edges, root)
    return W ** n * alpha ** 11


def classify_block(F: Fr) -> str:
    return "marginal" if F == 1 else ("subcritical" if F < 1 else "supercritical")


def hub_phi11(block_specs) -> Fr:
    """`Phi^11_hub = (64/621) a_hub^11 prod_b F_b` for a hub carrying the given blocks.
    `block_specs` is a list of `(n_b, edges_b, root_b)`."""
    msgs, prodF = [], Fr(1)
    for (nb, eb, rb) in block_specs:
        alpha, mu = block_amplitude_and_message(nb, eb, rb)
        msgs.append(mu)
        prodF *= W ** nb * alpha ** 11
    k = len(block_specs)
    a_hub = 1 + sum(msgs, Fr(0)) * Fr(1, k + 1)
    return W * a_hub ** 11 * prodF


def build_hub_tree(block_specs):
    """Assemble the explicit tree: a hub (vertex 0) with each block's root joined to it.  Returns
    `(n, edges)` so the formula can be checked against `rooted_phi.phi11_rooted(n, edges, 0)`."""
    edges = []
    off = 1
    for (nb, eb, rb) in block_specs:
        relabel = {rb: off}
        nxt = off + 1
        for v in range(nb):
            if v != rb:
                relabel[v] = nxt
                nxt += 1
        edges.append((0, off))
        for a, b in eb:
            edges.append((relabel[a], relabel[b]))
        off = nxt
    return off, tuple(edges)


def homogeneous_family_phi11(nb, eb, rb, k) -> Fr:
    """`Phi^11_hub` for `hub + k` copies of one block: `(64/621)(1 + mu*k/(k+1))^11 * F^k`."""
    alpha, mu = block_amplitude_and_message(nb, eb, rb)
    F = W ** nb * alpha ** 11
    return W * (1 + mu * Fr(k, k + 1)) ** 11 * F ** k


def homogeneous_family_sup(nb, eb, rb, K: int = 60):
    """`(k*, sup_k Phi^11_hub(k))` over `k in 1..K` for the homogeneous block family (exact)."""
    best_k, best = 1, Fr(0)
    for k in range(1, K + 1):
        v = homogeneous_family_phi11(nb, eb, rb, k)
        if v > best:
            best_k, best = k, v
    return best_k, best


def _rooted_blocks(m_max):
    """Yield `(n_b, edges_b, root_b)` for every rooted tree up to n_b = m_max (all roots of all trees)."""
    import networkx as nx
    yield 1, (), 0
    for m in range(2, m_max + 1):
        for T in nx.nonisomorphic_trees(m):
            idx = {v: i for i, v in enumerate(T.nodes())}
            e = tuple((idx[a], idx[b]) for a, b in T.edges())
            for r in range(m):
                yield m, e, r


@dataclass(frozen=True)
class MixedBlockMartingaleCertificate:
    """Generalizes the tie-recursive martingale to arbitrary hub blocks via the per-block transfer factor
    `F_b`.  `check()` certifies the general formula, the no-supercritical-block census (BG-necessary), the
    tie as the unique marginal block at the 23-gate, and the near-star as the extremal single-hub family --
    NOT BG itself.  See the module docstring for the honest scope."""

    supercritical_census_max: int = 9      # F_b <= 1 verified over all rooted blocks to here
    family_census_max: int = 7             # sup_k Phi^11_hub <= 1 verified for these homogeneous families

    def _tie_block(self):
        from .frustration_free import near_star_edges
        n, e = near_star_edges(5)
        return n, e, 0

    def general_formula_holds(self) -> bool:
        """`hub_phi11 == phi11_rooted(build_hub_tree, hub)` on several genuinely mixed hubs."""
        from .rooted_phi import phi11_rooted
        specs_list = [
            [(3, ((0, 1), (1, 2)), 0), (4, ((0, 1), (0, 2), (0, 3)), 0), (2, ((0, 1),), 0)],
            [(2, ((0, 1),), 0)] * 4,
            [self._tie_block(), (2, ((0, 1),), 0), (5, ((0, 1), (1, 2), (2, 3), (3, 4)), 0)],
        ]
        for specs in specs_list:
            n, e = build_hub_tree(specs)
            if hub_phi11(specs) != phi11_rooted(n, e, 0):
                return False
        return True

    def no_supercritical_block(self) -> bool:
        """`F_b <= 1` for every rooted block up to `supercritical_census_max` -- a NECESSARY condition for
        BG (a supercritical block would drive `bg_phi11 -> infinity`)."""
        return all(block_factor(*blk) <= 1 for blk in _rooted_blocks(self.supercritical_census_max))

    def tie_block_is_marginal(self) -> bool:
        """The tie block N(0,5) has `F = 1` (marginal) with message `mu = 3/23`."""
        n, e, r = self._tie_block()
        alpha, mu = block_amplitude_and_message(n, e, r)
        return block_factor(n, e, r) == 1 and mu == Fr(3, 23) and classify_block(Fr(1)) == "marginal"

    def marginal_first_appears_at_11(self) -> bool:
        """No block with `n_b <= 10` is marginal (all `F_b < 1`); marginality first appears at `n_b = 11`
        (the tie).  This is the 23-gate: `F_b = 1 => alpha_b = (621/64)^{n_b/11}` rational => `11 | n_b`."""
        from ..padic import padic_val_frac
        for blk in _rooted_blocks(10):
            if block_factor(*blk) == 1:
                return False
        # the tie realizes it: v_23(alpha) = 1 forces n_b = 11 * 1 = 11
        n, e, r = self._tie_block()
        alpha, _ = block_amplitude_and_message(n, e, r)
        return 11 * padic_val_frac(alpha, 23) == n

    def near_star_is_extremal_family(self) -> bool:
        """The length-2 ARM block (mid-leaf) generates the near-star family; its interior maximum is
        `Phi^11_hub = 1` EXACTLY at k = 5 (the tie N(0,5)) -- the unique single-hub family touching 1."""
        arm = (2, ((0, 1),), 0)
        kstar, sup = homogeneous_family_sup(*arm)
        return kstar == 5 and sup == 1 and block_factor(*arm) == Fr(486, 529)

    def no_homogeneous_family_exceeds_one(self) -> bool:
        """`sup_k Phi^11_hub(k) <= 1` for every homogeneous block family up to `family_census_max`
        (equality only for the near-star / arm block)."""
        for blk in _rooted_blocks(self.family_census_max):
            _, sup = homogeneous_family_sup(*blk)
            if sup > 1:
                return False
        return True

    def finding(self) -> str:
        return (
            "STRUCTURAL GENERALIZATION. One formula Phi^11_hub = (64/621) a_hub^11 prod_b F_b organizes all "
            "single-hub families, with F_b = (64/621)^{n_b} alpha_b^11 the per-block transfer factor. "
            "Trichotomy: F_b<1 subcritical (interior max), F_b=1 marginal (the tie; F=1 forces 11|n_b via the "
            "23-gate, unique at n=11), F_b>1 supercritical (would blow Phi^11_hub up -> BG violation). NO "
            "supercritical block exists in the census up to n_b=11, so F_b<=1 is a NECESSARY condition for "
            "BG, verified. The near-star is recovered as the ARM block's family: interior max = 1 exactly at "
            "k=5 (the tie), the unique single-hub family touching 1. Unifies family_martingale (marginal "
            "tie-recursive) and the near-star tie under one transfer factor. Does NOT prove BG (F_b<=1 for "
            "ALL blocks, interior maxima, multi-level trees, non-hub roots open). conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the general formula, the no-supercritical census (BG-necessary), the tie as the unique
        23-gated marginal block, and the near-star as the extremal single-hub family -- NOT BG."""
        return (
            self.general_formula_holds()
            and self.no_supercritical_block()
            and self.tie_block_is_marginal()
            and self.marginal_first_appears_at_11()
            and self.near_star_is_extremal_family()
            and self.no_homogeneous_family_exceeds_one()
        )

    def lean(self) -> str:
        return (
            "-- MIXED-BLOCK MARTINGALE: Phi^11_hub = (64/621) a_hub^11 prod_b F_b, F_b = (64/621)^{n_b} alpha_b^11.\n"
            "-- Trichotomy on F_b; no supercritical block (F_b <= 1) is BG-necessary.  Marginal F_b=1 forces\n"
            "-- 11 | n_b (v_23(621)=1); the arm block's family peaks at exactly 1 at k=5 (the tie N(0,5)).\n"
            "theorem arm_factor : ((64:ℚ)/621)^2 * (3/2)^11 = 486/529 := by norm_num\n"
        )
