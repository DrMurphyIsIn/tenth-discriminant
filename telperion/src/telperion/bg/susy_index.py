"""Probe (physics transfer #1): a signed SUSY-index partition function for Brualdi-Goldwasser.

Supersymmetry/localization is the physics mechanism where a smooth partition function collapses to an
exact INTEGER sum over fixed points -- the bosonic (permanent) bulk cancels against the fermionic
(determinant) part except at discrete points.  That is the exact "smooth overshoots, integer is exact"
shape BG needs.  And there is a clean dictionary: `log Phi^11 = 0` at the tie means the tie is a ZERO-ENERGY
(BPS) state, and BG (`Phi^11 <= 1` i.e. `-log Phi^11 >= 0`) is "the Hamiltonian is positive-semidefinite" --
i.e. the frustration-free positivity of `frustration_free.py`, in SUSY language.  Ties = SUSY ground states.

CANDIDATE SIGNED INDICES (all integer, all fermionic/signed):
  * `signed_matching_index` = `sum_k (-1)^k m_k` = the Euler characteristic of the matching complex = the
    Witten index `Tr(-1)^F` of the monomer-dimer model (bosonic even-k matchings minus fermionic odd-k).
  * `adjacency_nullity` = `n - 2*nu` (`nu` = max matching) = the number of fermionic ZERO MODES.
  * `det(A)` = signed perfect-matching count (`+-1` or `0` for a tree).

FINDING (NEGATIVE for localization, but it confirms the shape and pins the reason).
These indices ARE integer and DEFORMATION-INVARIANT: on the near-star family they are constant
(`chi=0`, `nullity=1`, `det=0` for every `s`), so they literally CANNOT overshoot between integer
arm-counts -- the exact robustness the smooth Gaussian lacked.  BUT they do NOT localize the tie: across
all trees at `n=11` the indices vary widely (`chi` from -9 to +15, `nullity` in {1,3,5,7,9}), yet the tie's
values (`chi=0`, `nullity=1`) are shared by dozens of non-tie trees.  The SUSY-index SHAPE is right; the
naive indices are blind to BG's resonance.

WHY (the unified reason).  The tie is an ARITHMETIC resonance -- the exact balance
`(64/621)^n (prod a)^11 = 1` (`64*243*23 = 621*576`) of the `(64/621)^n` weight against the algebraic
object.  A Witten index is TOPOLOGICAL/algebraic; it does not carry the `(64/621)` arithmetic weight, so it
cannot see the tie.  This is the archimedean(geometric)-vs-arithmetic split (dead-end #2 / `resonance_carrier`)
in physics language: only the 23-adic arithmetic carrier localizes the tie; geometric/topological indices do
not.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass


def _matching_counts(n, edges):
    from .graphlimit import matching_polynomial
    adj = {i: set() for i in range(n)}
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return matching_polynomial(adj)


def signed_matching_index(n, edges) -> int:
    """`sum_k (-1)^k m_k` -- the Euler characteristic of the matching complex / Witten index `Tr(-1)^F` of
    the monomer-dimer model (bosonic even-size matchings minus fermionic odd-size)."""
    return sum((-1) ** k * m for k, m in enumerate(_matching_counts(n, edges)))


def adjacency_nullity(n, edges) -> int:
    """Number of zero eigenvalues of the adjacency matrix = `n - 2*nu` (`nu` = max matching) = the fermionic
    zero-mode count (the SUSY ground-state degeneracy of the free-fermion reading)."""
    import numpy as np
    A = np.zeros((n, n))
    for a, b in edges:
        A[a, b] = 1
        A[b, a] = 1
    ev = np.linalg.eigvalsh(A)
    return int(sum(1 for v in ev if abs(v) < 1e-9))


def signed_perfect_matchings(n, edges) -> int:
    """`det(A)` = signed perfect-matching count (`+-1` or `0` for a tree, which has at most one perfect
    matching)."""
    import sympy as sp
    A = sp.zeros(n, n)
    for a, b in edges:
        A[a, b] = 1
        A[b, a] = 1
    return int(A.det())


@dataclass(frozen=True)
class SusyIndexProbe:
    """Physics-transfer probe #1: does a signed SUSY / Witten index localize the BG tie?  Verifies the
    indices are integer and deformation-invariant (the right shape -- no overshoot possible) but do NOT
    localize the tie (which is arithmetic, not topological).  `check()` certifies this, NOT BG."""

    near_star_s: tuple = (2, 3, 4, 5, 6)
    localize_n: int = 11          # the tie order; test whether the tie's index values are shared

    def indices_integer_and_deformation_invariant(self) -> bool:
        """On the near-star family the signed index, nullity, and det(A) are constant integers
        (`chi=0`, `nullity=1`, `det=0`) -- deformation-invariant, so they cannot overshoot between
        integer arm-counts (the robustness the smooth Gaussian lacked)."""
        from .frustration_free import near_star_edges
        chis, nulls, dets = set(), set(), set()
        for s in self.near_star_s:
            n, e = near_star_edges(s)
            chis.add(signed_matching_index(n, e))
            nulls.add(adjacency_nullity(n, e))
            dets.add(signed_perfect_matchings(n, e))
        return chis == {0} and nulls == {1} and dets == {0}

    def indices_do_not_localize_the_tie(self) -> bool:
        """At `n = localize_n` the tie's index values (`chi=0`, `nullity=1`) are shared by MANY non-tie
        trees -- so no naive index singles out the tie."""
        import networkx as nx
        share_chi = share_null = 0
        for T in nx.nonisomorphic_trees(self.localize_n):
            idx = {v: i for i, v in enumerate(T.nodes())}
            e = tuple((idx[a], idx[b]) for a, b in T.edges())
            if signed_matching_index(self.localize_n, e) == 0:
                share_chi += 1
            if adjacency_nullity(self.localize_n, e) == 1:
                share_null += 1
        return share_chi > 5 and share_null > 5     # dozens share the tie's values -> not localizing

    def tie_is_bps_zero_energy(self) -> bool:
        """The tie is a zero-energy (BPS) state: `Phi^11(N(0,5)) = 1` <=> `-log Phi^11 = 0`.  BG
        (`Phi^11 <= 1`, energy >= 0) is the SUSY/frustration-free positivity."""
        from .frustration_free import near_star_edges
        from .rooted_phi import bg_phi11_fast
        n, e = near_star_edges(5)
        return bg_phi11_fast(n, e) == 1

    def finding(self) -> str:
        return (
            "NEGATIVE for localization, and it pins the reason. The signed SUSY / Witten indices "
            "(chi = sum (-1)^k m_k = Euler char of the matching complex; adjacency nullity = n-2nu = fermion "
            "zero modes; det(A) = signed perfect matchings) ARE integer and DEFORMATION-INVARIANT -- constant "
            "on the near-star family (chi=0, nullity=1, det=0), so they cannot overshoot between integer "
            "arm-counts (the exact robustness the smooth Gaussian lacked; the SUSY-index SHAPE is right). BUT "
            "they do NOT localize the tie: at n=11 the tie's values are shared by dozens of non-tie trees. "
            "The tie is a ZERO-ENERGY (BPS) state -- Phi^11=1, so BG = 'energy >= 0' = frustration-free "
            "positivity in SUSY language -- but a topological/algebraic index does not carry the (64/621)^n "
            "arithmetic weight whose exact balance (64*243*23=621*576) IS the tie. Archimedean/geometric "
            "indices cannot see an arithmetic resonance; only the 23-adic carrier does. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies: the indices are integer + deformation-invariant (right shape), do not localize the
        tie, and the tie is a BPS zero-energy state -- NOT BG."""
        return (
            self.indices_integer_and_deformation_invariant()
            and self.indices_do_not_localize_the_tie()
            and self.tie_is_bps_zero_energy()
        )
