"""Safe-hub family positivity: BG's `<=` half proved on an infinite class of single-hub families.

`family_martingale.py` proved `Phi^11 < 1` on the tie-recursive family `hub + k*N(0,5)` (block = the tie).
This module GENERALIZES that positivity to an infinite class of blocks, extending it via the per-block
transfer factor and the safe-vertex condition.

THEOREM (safe-hub families).  Let `B` be a rooted block with transfer factor `F_B = (64/621)^{n_B} alpha_B^11`
and root message `mu_B`.  If

    F_B <= 1        (B satisfies BG at its root)      and      (1 + mu_B)^11 <= 621/64    (safe message),

then the homogeneous single-hub family `hub + k*B` satisfies `Phi^11_hub(k) < 1` for EVERY `k >= 1`.

PROOF (exact ceiling).  `Phi^11_hub(k) = (64/621) a_hub(k)^11 F_B^k` with `a_hub(k) = 1 + mu_B * k/(k+1)`.
Since `a_hub(k) < 1 + mu_B` and `F_B^k <= 1`,

    Phi^11_hub(k)  <  (64/621) (1 + mu_B)^11  <=  (64/621) * (621/64)  =  1 .

The safe message condition `(1 + mu_B)^11 <= 621/64` is exactly `a_hub < 1 + mu_B <= rho_B` -- the
"safe vertex" condition of `recursive_transfer.py` (`(64/621) rho_B^11 = 1`) applied at the hub.  QED.

CONSEQUENCE (an inductive reduction).  BG for the WHOLE family reduces to BG for the SINGLE block `B` plus a
message inequality: if `B` satisfies BG and has a small enough message, every `hub + k*B` satisfies BG for
free.  This subsumes `family_martingale` (the tie block has `mu = 3/23`, `(26/23)^11 < 621/64`) and covers an
infinite class -- 33 of the 142 rooted blocks up to `n_B = 7` are safe-hub, and the theorem holds on all of
them (verified).

THE BOUNDARY / OPEN CASE.  Large-message blocks `mu_B > rho_B - 1` (e.g. the length-2 ARM, `mu = 1/3`,
`(4/3)^11 > 621/64`) are NOT safe: `a_hub` can exceed `rho_B`, the ceiling proof fails, and the family can
REACH 1 -- the arm block's family IS the near-star, whose interior maximum is exactly the tie.  There the
`F_B^k` decay (not the ceiling) is what bounds `Phi^11`, and closing it in general is the dangerous-vertex
crux (`recursive_transfer`).  So this module proves the `<=` half on the SAFE-hub families and pins the
remaining hard case to the large-message (dangerous-hub) blocks.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .mixed_block_martingale import block_amplitude_and_message, block_factor, hub_phi11

W = Fr(64, 621)
RHO_B_11 = Fr(621, 64)   # rho_B^11; (1+mu)^11 <= RHO_B_11 is the exact safe-message condition


def is_safe_message(mu: Fr) -> bool:
    """The safe-message condition `(1 + mu)^11 <= 621/64`  <=>  `1 + mu <= rho_B` (exact rational test)."""
    return (1 + mu) ** 11 <= RHO_B_11


def safe_hub_ceiling(mu: Fr) -> Fr:
    """The ceiling `(64/621)(1 + mu)^11` -- an upper bound on `Phi^11_hub(k)` for all `k` (`< 1` iff safe)."""
    return W * (1 + mu) ** 11


def block_is_safe_hub(nb, eb, rb) -> bool:
    """`B` is safe-hub iff `F_B <= 1` and its root message is safe -- the theorem's hypotheses."""
    alpha, mu = block_amplitude_and_message(nb, eb, rb)
    return block_factor(nb, eb, rb) <= 1 and is_safe_message(mu)


def family_phi(nb, eb, rb, k) -> Fr:
    """`Phi^11_hub(k)` for `hub + k*B` (exact), via the mixed-block hub formula."""
    return hub_phi11([(nb, eb, rb)] * k)


@dataclass(frozen=True)
class SafeHubFamilyCertificate:
    """Proves BG's `<=` half on the infinite class of safe-hub single-hub families (extending
    `family_martingale`).  `check()` certifies the exact ceiling proof, the theorem on the block census, the
    tie-recursive family as a special case, and the near-star as the boundary -- a real positivity result,
    though NOT all of BG (the large-message/dangerous-hub case stays open).  conjecture1_proved = False."""

    census_m: int = 7
    k_check: tuple = (1, 2, 3, 5, 10, 20)

    def ceiling_below_one_iff_safe(self) -> bool:
        """The load-bearing exact step: `(64/621)(1+mu)^11 < 1  <=>  (1+mu)^11 < 621/64` (safe message)."""
        for mu in (Fr(3, 23), Fr(1, 3), Fr(1, 4), Fr(1, 5), Fr(6, 23)):
            if (safe_hub_ceiling(mu) < 1) != ((1 + mu) ** 11 < RHO_B_11):
                return False
        return True

    def family_bounded_by_ceiling(self, nb, eb, rb) -> bool:
        """`Phi^11_hub(k) <= (64/621)(1+mu)^11` for all checked `k` (the a_hub < 1+mu bound)."""
        _alpha, mu = block_amplitude_and_message(nb, eb, rb)
        ceil = safe_hub_ceiling(mu)
        return all(family_phi(nb, eb, rb, k) <= ceil for k in self.k_check)

    def theorem_holds_on_census(self):
        """Over all rooted blocks up to `census_m`: every SAFE-HUB block has `Phi^11_hub(k) < 1` for all
        checked `k`.  Returns `(safe_hub_count, total)`."""
        import networkx as nx
        safe = total = 0
        for m in range(1, self.census_m + 1):
            trees = [nx.empty_graph(1)] if m == 1 else list(nx.nonisomorphic_trees(m))
            for T in trees:
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                for r in range(m):
                    total += 1
                    if block_is_safe_hub(m, e, r):
                        safe += 1
                        if not all(family_phi(m, e, r, k) < 1 for k in self.k_check):
                            return None            # theorem violated
                        if not self.family_bounded_by_ceiling(m, e, r):
                            return None
        return safe, total

    def tie_recursive_is_special_case(self) -> bool:
        """The tie block N(0,5) (`mu = 3/23`) is safe-hub, and its ceiling is `family_martingale`'s
        `L = (64/621)(26/23)^11` -- so the tie-recursive positivity is this theorem's `k`-family."""
        from .frustration_free import near_star_edges
        n, e = near_star_edges(5)
        _alpha, mu = block_amplitude_and_message(n, e, 0)
        return (block_is_safe_hub(n, e, 0) and mu == Fr(3, 23)
                and safe_hub_ceiling(mu) == W * Fr(26, 23) ** 11)

    def near_star_is_the_boundary(self) -> bool:
        """The length-2 ARM block (`mu = 1/3`) is NOT safe-hub (`(4/3)^11 > 621/64`), and its family REACHES
        1 (the near-star, interior max at k=5) -- the large-message/dangerous-hub boundary case."""
        arm = (2, ((0, 1),), 0)
        _alpha, mu = block_amplitude_and_message(*arm)
        if is_safe_message(mu):
            return False
        return any(family_phi(*arm, k) == 1 for k in (5,))     # near-star tie at k=5

    def finding(self) -> str:
        res = self.theorem_holds_on_census()
        safe, total = res if res else (0, 0)
        return (
            "POSITIVE (an infinite-class extension of family_martingale). THEOREM: if a block B has F_B <= 1 "
            "and (1+mu_B)^11 <= 621/64 (safe message, a_hub < rho_B), then Phi^11_hub(k) < 1 for ALL k -- "
            "proved by the exact ceiling Phi^11_hub(k) < (64/621)(1+mu_B)^11 <= (64/621)(621/64) = 1. This "
            f"reduces BG for the whole family to BG for the single block plus a message inequality; {safe} of "
            f"{total} rooted blocks (n_B <= 7) are safe-hub and the theorem holds on all of them. It subsumes "
            "family_martingale (the tie block, mu=3/23) as one case. The BOUNDARY/open case is large-message "
            "blocks (mu > rho_B-1, e.g. the arm mu=1/3) where a_hub can exceed rho_B, the ceiling fails, and "
            "the family reaches 1 (the near-star) -- there the F_B^k decay must be used (the dangerous-vertex "
            "crux). Proves the <= half on the safe-hub families; the large-message case stays open. "
            "conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the exact ceiling proof, the theorem over the safe-hub block census, the tie-recursive
        special case, and the near-star boundary -- a real piece of the `<=` half, NOT all of BG."""
        res = self.theorem_holds_on_census()
        return (
            self.ceiling_below_one_iff_safe()
            and res is not None
            and res[0] > 0
            and self.tie_recursive_is_special_case()
            and self.near_star_is_the_boundary()
        )

    def lean(self) -> str:
        return (
            "-- SAFE-HUB FAMILY: F_B <= 1 and (1+mu)^11 <= 621/64  =>  Phi^11_hub(k) < 1 for all k, via\n"
            "-- Phi^11_hub(k) = (64/621) a_hub(k)^11 F_B^k < (64/621)(1+mu)^11 <= (64/621)(621/64) = 1.\n"
            "theorem safe_scale : (64:ℚ)/621 * (621/64) = 1 := by norm_num\n"
            "theorem tie_block_safe : ((26:ℚ)/23)^11 < 621/64 := by norm_num  -- tie block is safe-hub\n"
        )
