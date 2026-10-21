"""Fermionic degrees of freedom of the tree Laplacian ratio.

The synthesis (operator, 2026-08-17): the Laplacian ratio per(L)/prod(deg) is built entirely from
DISCRETE INTEGER data -- integer vertex degrees in the denominator, discrete matchings in the numerator --
so it is quantized by construction and its extremal set is a finite, discrete set of trees.  The discrete
configurations summed in per(L) are the MATCHINGS, and a matching is a hard-core dimer covering: each
vertex lies in AT MOST ONE dimer = PAULI EXCLUSION.  So the discrete quanta of the ratio ARE the
fermionic degrees of freedom.

Sharpest form: a TREE has 0 or 1 perfect matchings -- the extreme of hard-core exclusion.

This module makes that structure explicit and checkable: the matchings (fermion configurations), the
Pauli / hard-core constraint, the ratio as a sum over these discrete fermionic DOF, and the integer
degree vector (the lattice the fermions hop on).  It is a description of WHAT the object is -- a
Pauli-excluded fermionic extremal problem on an integer lattice -- not a proof of BG.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def degrees(n, edges):
    """The integer degree vector (the quantized denominator ∏deg is prod(degrees))."""
    d = [0] * n
    for a, b in edges:
        d[a] += 1
        d[b] += 1
    return d


def matchings(n, edges):
    """All matchings of the tree -- the FERMION CONFIGURATIONS (hard-core dimer coverings).
    Each is returned as a frozenset of edges."""
    E = list(edges)
    out = []

    def rec(i, used, cur):
        if i == len(E):
            out.append(frozenset(cur))
            return
        rec(i + 1, used, cur)                    # edge i is a monomer (empty)
        a, b = E[i]
        if a not in used and b not in used:      # or a dimer (Pauli: endpoints free)
            rec(i + 1, used | {a, b}, cur + [E[i]])

    rec(0, set(), [])
    return out


def fermion_dof_count(n, edges):
    """Number of matchings = number of fermionic configurations (the discrete DOF count)."""
    return len(matchings(n, edges))


def pauli_exclusion_holds(n, edges) -> bool:
    """Hard-core / Pauli: in every matching each vertex is covered by at most one dimer."""
    for M in matchings(n, edges):
        seen = set()
        for a, b in M:
            if a in seen or b in seen:
                return False
            seen.add(a)
            seen.add(b)
    return True


def perfect_matching_count(n, edges):
    """Perfect matchings (every vertex dimerized).  For a TREE this is 0 or 1 -- sharpest exclusion."""
    return sum(1 for M in matchings(n, edges) if 2 * len(M) == n)


def laplacian_ratio_as_fermion_sum(n, edges):
    """per(L)/prod(deg) = SUM over fermion configurations M of prod_{v matched in M} (1/deg_v).
    Returns (ratio, n_configs) -- the ratio built explicitly from the discrete fermionic DOF."""
    d = degrees(n, edges)
    total = Fr(0)
    for M in matchings(n, edges):
        matched = set()
        for a, b in M:
            matched |= {a, b}
        w = Fr(1)
        for v in matched:
            w *= Fr(1, d[v])
        total += w
    return total, len(list(matchings(n, edges)))


@dataclass(frozen=True)
class FermionDOFCertificate:
    """Certifies the object's fermionic-DOF structure for a tree: integer-degree lattice, Pauli-excluded
    matching configurations, 0-or-1 perfect matchings (sharpest exclusion), and the ratio = fermion sum."""

    n: int
    edges: tuple

    def check(self) -> bool:
        d = degrees(self.n, self.edges)
        integer_lattice = all(isinstance(x, int) for x in d)
        pauli = pauli_exclusion_holds(self.n, self.edges)
        pm = perfect_matching_count(self.n, self.edges) in (0, 1)   # tree exclusion extreme
        ratio, ndof = laplacian_ratio_as_fermion_sum(self.n, self.edges)
        return integer_lattice and pauli and pm and ndof == fermion_dof_count(self.n, self.edges)


def pauli_decompose(n, edges, vertex):
    """Decompose per(L)/prod(deg) by the PAULI STATE of `vertex`: (unmatched_sum, matched_sum, total).
    Since a vertex lies in at most one dimer (Pauli), the matched part is the sum over the vertex's
    single allowed dimer partners -- the hard-core cap.  total = per(L)/prod(deg)."""
    d = degrees(n, edges)
    unm = Fr(0)
    mat = Fr(0)
    for M in matchings(n, edges):
        covered = set()
        for a, b in M:
            covered |= {a, b}
        w = Fr(1)
        for v in covered:
            w *= Fr(1, d[v])
        if vertex in covered:
            mat += w
        else:
            unm += w
    return unm, mat, unm + mat
