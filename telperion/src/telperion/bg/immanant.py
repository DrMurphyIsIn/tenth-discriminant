"""General immanants of tree Laplacians -- the S_n / parastatistics toolkit.

For a tree, every immanant is a matching sum reweighted by the character on involutions (perm_dominance
proves this collapse):

    imm_lambda(L) = SUM_{matchings M} chi_lambda(sigma_M) * prod_{v unmatched} deg(v),

interpolating the fermion (lambda = 1^n, sign character = det, -> 0) and boson (lambda = (n), trivial
character = per) ends via the S_n irreps (parastatistics, Green 1953).  This module exposes the general
immanant and the normalized immanant d_lambda = imm_lambda / chi_lambda(1) for ANY partition, completing
the S_n pillar of the fermionic toolkit (perm_dominance covered only the boson-dominance inequality).
"""
from __future__ import annotations

from fractions import Fraction as Fr

from .perm_dominance import _matching_weights, _partitions, char_involution, dim


def immanant(n, edges, lam):
    """imm_lambda(L) of the tree Laplacian via the matching expansion (exact integer)."""
    mw = _matching_weights(n, edges)
    return sum(char_involution(list(lam), n, k) * w for k, w in mw)


def normalized_immanant(n, edges, lam):
    """d_lambda(L) = imm_lambda(L) / chi_lambda(1) (the normalized / per-degree-of-freedom immanant)."""
    return Fr(immanant(n, edges, lam), dim(list(lam), n))


def permanent(n, edges):
    """per(L) = imm_(n)(L) = matching sum, the bosonic end."""
    return immanant(n, edges, (n,))


def determinant(n, edges):
    """det(L) = imm_(1^n)(L), the fermionic end (= 0 for a connected graph)."""
    return immanant(n, edges, tuple([1] * n))


def parastatistics_spectrum(n, edges):
    """{lambda: d_lambda(L)} over all partitions -- the full boson<->fermion (parastatistics) interpolation
    for the tree Laplacian.  Ordered nowhere in particular; keys are partition tuples."""
    return {lam: normalized_immanant(n, edges, lam) for lam in _partitions(n)}


def permanental_dominance_holds(n, edges) -> bool:
    """Verify per(L) >= d_lambda(L) for all lambda (the proven tree/forest fact) on this instance."""
    pd = Fr(permanent(n, edges))
    return all(normalized_immanant(n, edges, lam) <= pd for lam in _partitions(n))
