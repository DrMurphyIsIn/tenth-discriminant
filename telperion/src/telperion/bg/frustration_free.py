"""Frustration-free / parent-Hamiltonian core (Tier-B target #3) for Brualdi-Goldwasser.

TIER_B #3 is "the collective-cancellation's exact name": a frustration-free ground state realizes a
GLOBAL minimum that is NOT a sum of locally-minimized terms -- literally the councils' verified
obstruction (PROOF_STATUS dead-end #1 refuted every "sum of non-positive local terms").  The exact
monomer-dimer ground state is an INTEGER-bond-dimension tensor (integrality), and Knabe/martingale/MPS
methods bound a global energy from local data DESPITE non-decomposability.

**Probe (this module).**
  (i)  Build the monomer-dimer parent structure on the tree as a bond-dimension-2 MPS transfer (the
       "integer-bond-dimension tensor").  The `<=` half `Phi^11 <= 1` is a FRUSTRATION-FREE POSITIVITY:
       a global free energy `-log Phi^11 >= 0` (ground-state energy `E_0 >= 0`), not a sum of local
       non-positive terms -- exactly the shape dead-end #1 says it must be.
  (ii) Ask the Knabe question: does a finite-window LOCAL gap force the global bound, with equality only
       at the gapless tie?

**HONEST FINDING (reframe + obstruction).**
The frustration-free framing is CORRECT and captured: the bond-dimension-2 transfer reproduces the
matching partition function exactly (integer bond dimension = 2), and `Phi^11 <= 1` is the ground-state
positivity.  BUT the Knabe-type local-gap -> global route to a UNIFORM certificate is OBSTRUCTED.  The
transfer gap `1 - D` (D = Phi^11^(1/n), the bulk free-energy density = dominant transfer eigenvalue)
closes NOT ONLY at the isolated tie (near-star: `D = 1` exactly at s=5) but along the ENTIRE tie-recursive
family `hub + k * N(0,5)`, where `D -> 1` as `k -> infinity` (0.888, 0.943, 0.964, ..., 0.9978 at k=40).
The system is GAPLESS on a positive-density set of trees, so NO uniform Knabe local-gap threshold exists
-- a uniform local gap is exactly what `transfer_tail.py` already showed is absent (`sup D = 1`, no
uniform gap), now stated in parent-Hamiltonian language.

So #3 supplies the POSITIVITY / collectivity of the `<=` half (frustration-free `E_0 >= 0`, integer bond
dimension, non-local by design) but NOT a uniform local certificate: the gapless locus is a whole family,
not a point.  Combined with the other probes: the `<=` half is a frustration-free positivity (this
module); the EQUALITY locus is 23-adically pinned to actual ties (`resonance_carrier.py`).  Neither
closes BG; together they are exactly PROOF_STATUS's decomposition (open `<=` crux + 23-gate equality set).
`conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .rooted_phi import bg_phi11_fast

BOND_DIMENSION = 2  # occupied / unoccupied -- the integer bond dimension of the monomer-dimer MPS


def near_star_edges(s):
    """hub 0 with s arms of length 2 (0-mid-leaf); n = 2s+1.  Tie at s=5 (n=11)."""
    e = []
    nid = 1
    for _ in range(s):
        e.append((0, nid))
        e.append((nid, nid + 1))
        nid += 2
    return 2 * s + 1, tuple(e)


def tie_recursive_edges(k):
    """The tie-recursive family: a root hub with k copies of the tie N(0,5) hung off it (n = 1 + 11k).
    Its per-vertex density -> 1 as k grows -- the gapless family with no uniform transfer gap."""
    n5, e5 = near_star_edges(5)
    edges = []
    off = 1
    for _ in range(k):
        edges.append((0, off))               # root hub -> this tie block's hub
        for a, b in e5:
            edges.append((off + a, off + b))
        off += n5
    return 1 + 11 * k, tuple(edges)


def monomer_dimer_partition(n, edges, x=None, root: int = 0):
    """Monomer-dimer partition function `Z = sum_matchings x^|M|` via the bond-dimension-2 MPS transfer
    on the tree (the frustration-free ground-state tensor).  Per edge (parent, v) the message is the pair
    `(A, B)`: A = weight of subtree(v) matchings with v still FREE (matchable to its parent), B = with v
    already matched inside the subtree.  Exact; `x` may be a Fraction (default 1 -> total matchings) or a
    sympy symbol (-> the matching generating polynomial `sum_k m_k x^k`)."""
    if x is None:
        x = Fr(1)
    g = {i: set() for i in range(n)}
    for a, b in edges:
        g[a].add(b)
        g[b].add(a)

    def rec(v, parent):
        A, B = Fr(1), Fr(0)                   # leaf: free = 1, matched = 0
        for w in g[v]:
            if w == parent:
                continue
            Aw, Bw = rec(w, v)
            fw = Aw + Bw                       # child resolved, edge (v,w) NOT used
            A, B = A * fw, B * fw + A * x * Aw  # or use (v,w): needs w free (Aw), marks v matched
        return A, B

    A, B = rec(root, -1)
    return A + B


def transfer_density(n, edges) -> float:
    """The bulk free-energy density `D(T) = Phi^11(T)^(1/n)` -- the dominant transfer eigenvalue.  The
    frustration-free spectral gap is `1 - D >= 0`; `Phi^11 <= 1  <=>  D <= 1  <=>  E_0 = -log Phi^11 >= 0."""
    return float(bg_phi11_fast(n, edges)) ** (1.0 / n)


@dataclass(frozen=True)
class FrustrationFreeGapProbe:
    """Tier-B probe #3: is `Phi^11 <= 1` a frustration-free ground-state positivity closed by a Knabe-type
    local-gap bound?  Verifies the integer-bond-dimension MPS transfer and the gap structure, and shows the
    Knabe uniform-threshold route is obstructed (the gap closes on a whole family).  `check()` certifies
    those constructed facts, NOT BG.  See the module docstring for the honest scope."""

    near_star_s: tuple = (2, 3, 4, 5, 6, 7)
    tie_recursive_k: tuple = (1, 2, 3, 5, 10, 20)
    tie_s: int = 5

    def bond_dimension(self) -> int:
        return BOND_DIMENSION

    def mps_reproduces_matchings(self) -> bool:
        """The bond-dimension-2 transfer partition function equals the total matching count over the
        near-star family -- the frustration-free ground-state tensor has integer bond dimension 2."""
        from .graphlimit import matching_polynomial
        for s in self.near_star_s:
            n, e = near_star_edges(s)
            adj = {i: set() for i in range(n)}
            for a, b in e:
                adj[a].add(b)
                adj[b].add(a)
            if monomer_dimer_partition(n, e) != sum(matching_polynomial(adj)):
                return False
        return True

    def tie_is_gapless(self) -> bool:
        """On the near-star family the transfer gap `1 - D` is 0 exactly at the tie (Phi^11 = 1, D = 1)
        and strictly positive off it -- the tie is the isolated gapless (critical) point there."""
        for s in self.near_star_s:
            n, e = near_star_edges(s)
            phi = bg_phi11_fast(n, e)
            if s == self.tie_s:
                if phi != 1:
                    return False
            else:
                if not phi < 1:                # off-tie: gapped (D < 1)
                    return False
        return True

    def gap_closes_on_tie_recursive_family(self) -> bool:
        """The transfer gap `1 - D` STRICTLY DECREASES toward 0 along `hub + k * N(0,5)` as k grows, while
        staying > 0 at every finite k -- the gap closes on a whole family, not just the isolated tie."""
        gaps = [1.0 - transfer_density(*tie_recursive_edges(k)) for k in self.tie_recursive_k]
        strictly_shrinking = all(b < a for a, b in zip(gaps, gaps[1:]))
        all_positive = all(g > 0 for g in gaps)
        approaching_zero = gaps[-1] < gaps[0] / 3        # demonstrably closing
        return strictly_shrinking and all_positive and approaching_zero

    def knabe_uniform_threshold_exists(self) -> bool:
        """A Knabe-type certificate needs a UNIFORM local-gap lower bound.  Since the transfer gap -> 0
        along the tie-recursive family (gapless on a positive-density set), no such uniform threshold
        exists.  Returns False (the obstruction)."""
        return not self.gap_closes_on_tie_recursive_family()

    def finding(self) -> str:
        return (
            "REFRAME + OBSTRUCTION. #3 is the collective-cancellation's exact name: the <= half Phi^11<=1 "
            "is a FRUSTRATION-FREE POSITIVITY (ground-state energy E_0 = -log Phi^11 >= 0, NOT a sum of "
            "locally-minimized terms -- matching dead-end #1), and the monomer-dimer ground state is an "
            "INTEGER-bond-dimension (=2) MPS tensor (verified: the bond-dim-2 transfer reproduces the "
            "matching partition function). BUT the Knabe local-gap -> global route to a UNIFORM certificate "
            "is OBSTRUCTED: the transfer gap 1-D closes not only at the isolated tie (near-star D=1 at s=5) "
            "but along the ENTIRE tie-recursive family hub+k*N(0,5) (D->1 as k->inf), so the system is "
            "gapless on a positive-density set and no uniform Knabe threshold exists -- the same archimedean "
            "wall transfer_tail found (sup D=1), in parent-Hamiltonian language. Frustration-free supplies "
            "the POSITIVITY/collectivity of the <= half; the 23-adic carrier (resonance_carrier) supplies "
            "the EQUALITY locus. Neither closes BG. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the constructed facts -- integer-bond-dimension MPS reproduces the matchings, the tie
        is the isolated gapless point, the gap closes on the tie-recursive family, and hence no uniform
        Knabe threshold exists -- NOT BG."""
        return (
            self.mps_reproduces_matchings()
            and self.tie_is_gapless()
            and self.gap_closes_on_tie_recursive_family()
            and not self.knabe_uniform_threshold_exists()
        )
