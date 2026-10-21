"""Arithmetic amplitude toolkit -- the Schrodinger / wave-function side, where topology is blind.

The Levinson-Friedel (topological) invariants -- phase shift, displaced charge, bound-state count -- do
NOT discriminate the near-star (every tree gives the same count).  Brualdi-Goldwasser extremality lives
entirely in the AMPLITUDE, which is the wave-function / Schrodinger side of the same physics.  This
module ports the arithmetic amplitude tools.

The exact factorization: Phi^11 = (64/621)^n * PROD_v a_v^11, with the per-vertex amplitude
    a_v = 1 + z_v S_v = z_v / m_v      (z_v = 3/(3 d_v + cr_v),  S_v = sum_children m_c),
where m_v is the cavity Green's function (recursive Schrodinger resolvent, Abou-Chacra-Anderson).  Hence

    BG:  Phi^11 <= 1   <=>   PROD_v a_v^11 <= (621/64)^n   <=>   geometric mean of a_v <= rho_B,
    rho_B = (621/64)^(1/11).

Verified: at the tie N(0,5), PROD a_v^11 = (621/64)^n EXACTLY (equality); the near-star amplitudes are
{1 (leaves), 3/2 (arm-mids), 23/18 (hub)} whose product is 621/64, and the 23 sits in the hub amplitude.

The near-star bound-state WAVE FUNCTION (top adjacency eigenvector) peaks on the hub -- amplitude
concentration = the resonance.  The proof target is arithmetic and VARIATIONAL: a per-vertex cavity
potential P(m) with  a_v <= rho_B * exp(P(m_v) - sum_c P(m_c))  telescopes to Phi <= 1, equality pinned
at the tie cavity m = 3/23.  (This is the open crux; no finite-basis P closes it -- the integrality wall.)
"""
from __future__ import annotations

from fractions import Fraction as Fr

_RHO_B_11 = Fr(621, 64)   # rho_B^11 = 3^3*23/2^6


def _rec_amp(cr, kids):
    """Returns (cavity m, amplitude a = 1+zS, list of all subtree amplitudes)."""
    ch = [_rec_amp(*k) for k in kids]
    S = sum(m for m, _, _ in ch)
    amps = []
    for _, _, sub in ch:
        amps += sub
    d = len(kids) + 1 + cr
    z = Fr(3, 3 * d + cr)
    a = 1 + z * S
    m = z / a
    return (m, a, amps + [a])


def vertex_amplitudes(cr, kids):
    """The per-vertex amplitudes a_v = 1 + z_v S_v (the Schrodinger normalizations) of the rooted tree."""
    return _rec_amp(cr, kids)[2]


def amplitude_product11(cr, kids):
    """PROD_v a_v^11 (exact Fraction) -- the BG amplitude quantity."""
    p = Fr(1)
    for a in vertex_amplitudes(cr, kids):
        p *= a ** 11
    return p


def bg_amplitude_holds(cr, kids):
    """BG in amplitude form: PROD_v a_v^11 <= (621/64)^n.  Returns (holds, product, benchmark)."""
    amps = vertex_amplitudes(cr, kids)
    n = len(amps)
    p = Fr(1)
    for a in amps:
        p *= a ** 11
    bench = _RHO_B_11 ** n
    return (p <= bench, p, bench)


def amplitude_gap(cr, kids):
    """(621/64)^n - PROD a_v^11 (>= 0 is BG; = 0 at the tie).  The exact amplitude slack."""
    holds, p, bench = bg_amplitude_holds(cr, kids)
    return bench - p


def cavity_potential_residual(cr, kids, P):
    """Per-vertex cavity-potential check: for each vertex, is  a_v <= rho_B * prod P-telescope ?
    Given a potential P: cavity(m)->Fraction-or-float, returns the worst per-vertex residual
    log(a_v) - (1/11)log(621/64) - (P(m_v) - sum_c P(m_c)); <= 0 for all v telescopes to Phi<=1.
    This exposes the OPEN target: find P making every residual <= 0 (equality at m=3/23)."""
    import math
    lb = math.log(float(_RHO_B_11)) / 11.0

    def rec(cr, kids):
        ch = [rec(*k) for k in kids]
        S = sum(m for m, _ in ch)
        d = len(kids) + 1 + cr
        z = Fr(3, 3 * d + cr)
        a = 1 + z * S
        m = z / a
        res = math.log(float(a)) - lb - (P(m) - sum(P(mc) for mc, _ in ch))
        worst = max([res] + [w for _, w in ch])
        return (m, worst)

    return rec(cr, kids)[1]
