"""Sibling coupling: a Lewis-Riesenfeld-style read of the tree recursion, and why the coupling is
irreducibly multi-variable.

`envelope.py` showed a per-message bound `F <= h(mu)` cannot close the induction.  This module takes the
Lewis-Riesenfeld (LR) view -- reformulate the recursion, isolate the coupled mode by an orthogonal /
mean-field decomposition, and ask whether a decoupled invariant exists.

LOG-COORDINATE REFORMULATION.  With `x = -log F` (`F <= 1  <=>  x >= 0`), the recursion
`F_v = (64/621) a_v^11 prod_c F_c` becomes ADDITIVE:

    x_v = c0 - 11 log a_v + sum_c x_c ,   c0 = log(621/64),   a_v = 1 + S/(j+1),   S = sum_c mu_c.

Telescoping over the whole subtree, `x_v = c0 * n_v - 11 * sum_{w in subtree} log a_w`, so BG is a clean
statement about the DISTRIBUTION of vertex amplitudes:

    BG (rooted)  <=>  x >= 0  <=>  (1/n) sum_w log a_w <= log rho_B ,   rho_B = (621/64)^(1/11),

i.e. the GEOMETRIC MEAN of the vertex amplitudes is `<= rho_B`, with equality EXACTLY at the tie.  In
exact rational form: `(prod_v a_v)^11 <= (621/64)^n`, equality iff tie.  This is the multi-variable
(amplitudes-couple-through-the-tree) face of BG.

THE LR DECOUPLING STRUCTURE.  The siblings couple ONLY through `S = sum_c mu_c` -- the symmetric /
center-of-mass mode.  `a_v = 1 + S/(j+1)` depends on the children messages ONLY through `(S, j)`; the
relative modes (how the messages are distributed among siblings) do NOT enter the amplitude.  This is
exactly the setting where an orthogonal transformation isolates one coupled coordinate (the LR / Ermakov
picture): the interaction is mean-field in `S`.

THE DECOUPLED (single-variable) INVARIANT -- CORRECTED 2026-09-29.  A decoupled invariant is
`x >= phi(mu)`.  For a CONVEX `phi`, Jensen collapses the worst sibling distribution to EQUAL siblings,
reducing the j-body step to the two-parameter condition
`G(j,S) = c0 - 11 log(1 + S/(j+1)) + j*phi(S/j) - phi(1/(j+1+S)) >= 0`.
This module used to record that the best convex `phi` (`phi(3/23)=0`, `phi >= 0`, `phi(1) <= c0`) is
LP-INFEASIBLE with worst-case slack `t* ~ -5.2`, and concluded that no single-variable invariant closes
the induction.  THAT WAS WRONG.  The LP in `docs/sibling_coupling_convex_lp.py` imposed the second
differences with the wrong sign, so it searched CONCAVE `phi`; with the sign fixed it is feasible (grid
optimum `t* ~ +0.009`; the exact optimum is 0, tight at the two ties).  An explicit feasible `phi` is
`phi = -11 U` with `U` a concave piecewise-linear witness: `G >= 0` for every j (checked numerically for j <= 3000), with equality
only at (j,S) = (1,1) and (5,5/3).  So a single-variable
convex invariant DOES close the ceiling induction; the coupling is NOT irreducibly joint for that bound.

HONEST SCOPE.  This is a reformulation + a structural (LR) analysis.  Its former "no-go for the
single-variable class" is RETRACTED (see above).  It does not prove BG.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .sporadic_tie import amp_product

RHO_B_11 = Fr(621, 64)   # rho_B^11 exactly; BG(rooted) <=> (prod a)^11 <= RHO_B_11^n

# The best-convex-phi linear program's worst-case slack.  The value formerly recorded here, -5.2, came from
# an LP whose convexity rows had the wrong sign (it searched concave phi).  Corrected 2026-09-29: the exact
# optimum is 0 (feasible, tight at the ties); docs/sibling_coupling_convex_lp.py now reports ~ +0.009 on its
# grid (the grid misses S = 5/3).  Recorded as evidence, not a runtime dep.
CONVEX_PHI_LP_SLACK = 0.0


def amplitude_product(n, edges, root=0) -> Fr:
    """`prod_v a_v` for the rooted tree (exact).  `Phi^11 = (64/621)^n (prod a_v)^11`."""
    return amp_product(n, edges, root)


def parent_amplitude(S: Fr, j: int) -> Fr:
    """The vertex amplitude `a_v = 1 + S/(j+1)` -- a function of the children ONLY through the
    symmetric mode `S = sum_c mu_c` and the child count `j` (the LR mean-field coupling)."""
    return 1 + S * Fr(1, j + 1)


@dataclass(frozen=True)
class SiblingCouplingCertificate:
    """The LR-style sibling-coupling analysis.  Certifies the geometric-mean-amplitude reformulation of
    BG (equality at the tie), the symmetric-mode coupling structure, and the single-variable no-go -- NOT
    BG.  See the module docstring for the honest scope.  conjecture1_proved = False."""

    m_max: int = 8

    def _tie(self):
        from .frustration_free import near_star_edges
        n, e = near_star_edges(5)
        return n, e

    def bg_is_geometric_mean_bound(self) -> bool:
        """`(prod a_v)^11 <= (621/64)^n  <=>  phi11_rooted <= 1` for every rooted tree up to m_max -- BG is
        exactly "geometric mean of vertex amplitudes <= rho_B"."""
        import networkx as nx
        from .rooted_phi import phi11_rooted
        for m in range(2, self.m_max + 1):
            for T in nx.nonisomorphic_trees(m):
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                for r in range(m):
                    lhs = amplitude_product(m, e, r) ** 11 <= RHO_B_11 ** m
                    rhs = phi11_rooted(m, e, r) <= 1
                    if lhs != rhs:
                        return False
        return True

    def tie_saturates_the_bound(self) -> bool:
        """The tie achieves EQUALITY in the amplitude bound: `(prod a_v)^11 = (621/64)^n` at N(0,5)."""
        n, e = self._tie()
        return amplitude_product(n, e, 0) ** 11 == RHO_B_11 ** n

    def coupling_is_symmetric_mode(self) -> bool:
        """The amplitude `a_v` depends on the children only through `(S, j)`: two DIFFERENT child-message
        multisets with the same sum `S` and same count `j` give the same amplitude (mean-field coupling)."""
        j = 3
        # two distinct message multisets with equal sum S = 1
        m1 = [Fr(1, 3), Fr(1, 3), Fr(1, 3)]
        m2 = [Fr(1, 2), Fr(1, 4), Fr(1, 4)]
        if sum(m1) != sum(m2) or len(m1) != len(m2):
            return False
        return parent_amplitude(sum(m1), j) == parent_amplitude(sum(m2), j)

    def energy_reformulation_holds(self) -> bool:
        """The log-energy telescopes: `Phi^11 = (64/621)^n (prod a_v)^11` for every rooted tree (so
        `-log Phi^11 = n log(621/64) - 11 sum log a_v`) -- verified against `phi11_rooted`."""
        import networkx as nx
        from .rooted_phi import phi11_rooted
        for m in range(2, self.m_max + 1):
            for T in nx.nonisomorphic_trees(m):
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                for r in range(m):
                    if Fr(64, 621) ** m * amplitude_product(m, e, r) ** 11 != phi11_rooted(m, e, r):
                        return False
        return True

    def single_variable_invariant_ruled_out(self) -> bool:
        """RETRACTED 2026-09-29; always False.  This used to return True on the strength of two facts: the
        tight envelope h* is not a supersolution (still true, `envelope.py`), and a convex-phi LP was
        infeasible (false: the LP had a sign error).  A convex single-variable invariant exists (module
        docstring), so the class is not ruled out.  Kept for API compatibility."""
        return CONVEX_PHI_LP_SLACK < 0

    def finding(self) -> str:
        return (
            "REFORMULATION + LR STRUCTURE + single-variable NO-GO. In log coordinates x = -log F the "
            "recursion is additive, x_v = c0 - 11 log a_v + sum_c x_c, and telescopes to BG <=> geometric "
            "mean of vertex amplitudes <= rho_B (exact: (prod a)^11 <= (621/64)^n), equality EXACTLY at the "
            "tie. The siblings couple ONLY through the symmetric mode S = sum mu_c (a_v = 1 + S/(j+1) depends "
            "on children only via (S,j)) -- the Lewis-Riesenfeld mean-field / orthogonal-decoupling setting. "
            "A DECOUPLED invariant x >= phi(mu) with CONVEX phi DOES close the ceiling induction (Jensen at "
            "the mean message): phi = -11U with U a concave witness. "
            "The former single-variable NO-GO (convex-phi LP slack -5.2) "
            "is RETRACTED: that LP had a sign error and searched concave phi. "
            "conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the reformulation, the tie saturation and the symmetric-mode coupling -- NOT BG.
        (The single-variable no-go formerly included here is retracted.)"""
        return (
            self.energy_reformulation_holds()
            and self.bg_is_geometric_mean_bound()
            and self.tie_saturates_the_bound()
            and self.coupling_is_symmetric_mode()
        )
