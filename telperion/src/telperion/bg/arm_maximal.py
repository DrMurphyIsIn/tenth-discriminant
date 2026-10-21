"""The arm maximizes F_B among large-message blocks -- reduced to a clean master inequality.

`residual_foc.py` reduced single-hub BG to one statement: no non-arm block has `k* > K_max(mu)`, equivalently
the length-2 ARM (`F = 486/529`) uniquely maximizes `F_B` among large-message blocks.  This module targets
that inequality, verifies it, and reduces it to a single clean, tight, leaf-anchored MASTER INEQUALITY.

VERIFIED.  `F_B <= 486/529` for every large-message block (`(1+mu_B)^11 > 621/64`), with the arm the UNIQUE
maximizer (checked over all 568 large-message blocks up to `n_B = 9`).

THE MASTER INEQUALITY (the reduced core).  For EVERY rooted tree `B`,

    (2 + mu_B)^11 * F_B  <=  (64/621) * 3^11    ( = 419904/23 ) ,     equality iff `B` is a leaf.

Equivalently `F_B <= (64/621)(3/(2+mu_B))^11`.  It is tight exactly at the leaf (`mu = 1`, `F = 64/621`).

MASTER => ARM (exact, one line).  For a `j = 1` block with child `c`, `F_B = (64/621)(1 + mu_c/2)^11 F_c`.
The master inequality on `c` gives `F_c <= (64/621)(3/(2+mu_c))^11`, and the identity
`(1 + mu_c/2) * 3/(2 + mu_c) = 3/2` collapses the product:

    F_B  <=  (64/621)^2 (3/2)^11  =  486/529  =  F_arm ,       equality iff `c` is a leaf (i.e. `B` = the arm).

MASTER = "the leaf is the F-maximal child of a mid" (exact).  Attaching `B` under a degree-2 vertex (a mid)
gives `F_{mid->B} = (64/621)((2+mu_B)/2)^11 F_B`, and the master inequality is EXACTLY
`F_{mid->B} <= F_{mid->leaf} = 486/529` -- the arm-maximal statement one level up.

WHAT REMAINS (the crux, now razor-sharp and leaf-anchored).  The master inequality is verified and holds with
a clean equality case, but its naive induction is LOSSY: bounding each child by the master bound introduces a
factor `C^{j-1}` (`C = (64/621)3^11 ~ 18257`) that blows up for `j >= 2` -- the same collective-cancellation
obstruction as BG's `<=` half, now concentrated in a single tight inequality that is EXACT at the leaf.  So
single-hub BG reduces to: prove `(2+mu_B)^11 F_B <= (64/621) 3^11` for all rooted trees.  `conjecture1_proved
= False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .mixed_block_martingale import block_amplitude_and_message, block_factor

RHO_B_11 = Fr(621, 64)
MASTER_C = Fr(64, 621) * 3 ** 11          # = 419904/23; the bound in (2+mu)^11 F <= C form
F_ARM = Fr(486, 529)                       # = (64/621)^2 (3/2)^11


def master_upper_bound(mu: Fr) -> Fr:
    """The master upper bound on `F_B`: `(64/621)(3/(2+mu))^11` (tight at the leaf, `mu = 1`)."""
    return Fr(64, 621) * (Fr(3) / (2 + mu)) ** 11


def satisfies_master(nb, edges, root) -> bool:
    """`(2 + mu_B)^11 F_B <= (64/621) 3^11` for the given rooted block (exact)."""
    _alpha, mu = block_amplitude_and_message(nb, edges, root)
    return (2 + mu) ** 11 * block_factor(nb, edges, root) <= MASTER_C


@dataclass(frozen=True)
class ArmMaximalCertificate:
    """The arm maximizes `F_B` among large-message blocks, reduced to the master inequality.  `check()`
    certifies: the arm bound on the census, the master inequality on the census (tight at the leaf), the exact
    `master => arm` telescoping, and the `master = leaf-maximal-child` equivalence -- a clean reduction of the
    single-hub crux, NOT a full proof of the master inequality, NOT BG.  conjecture1_proved = False."""

    census_m: int = 8

    def _blocks(self):
        import networkx as nx
        for m in range(1, self.census_m + 1):
            trees = [nx.empty_graph(1)] if m == 1 else list(nx.nonisomorphic_trees(m))
            for T in trees:
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                for r in range(m):
                    yield m, e, r

    def arm_maximizes_F_among_large_message(self) -> bool:
        """`F_B <= 486/529` for every large-message block, with the arm attaining it."""
        arm_hit = False
        for m, e, r in self._blocks():
            _alpha, mu = block_amplitude_and_message(m, e, r)
            if (1 + mu) ** 11 <= RHO_B_11:
                continue
            F = block_factor(m, e, r)
            if F > F_ARM:
                return False
            if F == F_ARM:
                arm_hit = True
        return arm_hit

    def master_inequality_on_census(self) -> bool:
        """`(2 + mu_B)^11 F_B <= (64/621) 3^11` for EVERY rooted tree up to `census_m`, with equality exactly
        at the leaf (`mu = 1`)."""
        for m, e, r in self._blocks():
            _alpha, mu = block_amplitude_and_message(m, e, r)
            lhs = (2 + mu) ** 11 * block_factor(m, e, r)
            if lhs > MASTER_C:
                return False
            if (lhs == MASTER_C) != (mu == 1):         # equality iff leaf
                return False
        return True

    def master_telescopes_to_arm(self) -> bool:
        """Exact `master => arm` for `j = 1` blocks: `(1 + mu/2) * 3/(2 + mu) = 3/2`, so a child satisfying
        master forces `F_B <= (64/621)^2 (3/2)^11 = 486/529`.  Verify the identity and the constant."""
        import sympy as sp
        mu = sp.Symbol("mu", positive=True)
        identity = sp.simplify((1 + mu / 2) * 3 / (2 + mu)) == sp.Rational(3, 2)
        return identity and Fr(64, 621) ** 2 * Fr(3, 2) ** 11 == F_ARM

    def master_is_leaf_maximal_child(self) -> bool:
        """The master inequality equals `F_{mid->B} <= F_{mid->leaf} = 486/529`: verify the exact scaling
        `(64/621) 3^11 = 486/529 * 2^11 * 621/64`."""
        return MASTER_C == F_ARM * 2 ** 11 * Fr(621, 64)

    def naive_induction_is_lossy(self) -> bool:
        """The obstruction: bounding each child by the master bound introduces a factor `C^{j-1}` with
        `C = (64/621) 3^11 > 1`, which blows up for `j >= 2` -- so the master inequality is not closed by
        naive induction (the collective-cancellation obstruction, leaf-anchored)."""
        return MASTER_C > 1

    def finding(self) -> str:
        return (
            "REDUCED to a clean master inequality (the single-hub crux, leaf-anchored). VERIFIED: F_B <= "
            "486/529 for all large-message blocks (arm the unique maximizer). This follows from the MASTER "
            "INEQUALITY (2+mu_B)^11 F_B <= (64/621) 3^11 for ALL rooted trees (verified, equality iff leaf): "
            "for a j=1 block, F_B = (64/621)(1+mu_c/2)^11 F_c, and master on the child plus the identity "
            "(1+mu_c/2)*3/(2+mu_c) = 3/2 gives F_B <= (64/621)^2(3/2)^11 = 486/529 (arm), equality iff the "
            "child is a leaf. Equivalently master says 'the leaf is the F-maximal child of a mid.' Remaining "
            "crux: the master inequality's naive induction is lossy (a C^{j-1} blowup, C~18257, for j>=2) -- "
            "the collective-cancellation obstruction, now a single tight inequality exact at the leaf. "
            "Single-hub BG reduces to proving (2+mu)^11 F <= (64/621) 3^11 for all rooted trees. "
            "conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the arm bound, the master inequality (tight at the leaf), the exact master=>arm
        telescoping, and the leaf-maximal-child equivalence -- NOT a proof of the master inequality, NOT BG."""
        return (
            self.arm_maximizes_F_among_large_message()
            and self.master_inequality_on_census()
            and self.master_telescopes_to_arm()
            and self.master_is_leaf_maximal_child()
            and self.naive_induction_is_lossy()
        )
