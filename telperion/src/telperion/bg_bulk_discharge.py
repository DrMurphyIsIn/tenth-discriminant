"""BG bulk-discharge engine — the analytic upper-bound route for the Laplacian ratio.

The classical-BG upper bound `F* = lim (1/n) log max_T pi(T) <= log(621/64)/11` reduces (see
`docs/BG_STAR_OF_BROOMS_RESULT.md` Sec 5b) to a POINTWISE discharge inequality via the exact Bethe/cavity
decomposition on trees:

    pi(T) = prod_v (1 + sum_{u~v} w_{uv} h_{u->v}) / prod_{(u,v)} (1 + w_{uv} h_{u->v} h_{v->u}),
    w_{uv} = 1/(d_u d_v),   h_{u->v} = 1/(1 + sum_{c in N(u)\\v} w_{uc} h_{c->u}) in (0,1].

so `log pi(T) = sum_v A_v - sum_e B_e` with `A_v = log(1 + sum w h)`, `B_e = log(1 + w h h)`.  For an
edge-discharge `tau` (`tau_{v,u} + tau_{u,v} = 1`) define the LOCAL free energy `phi_v = A_v - sum_u tau_{v,u}
B_{v,u}`.  Then `log pi(T) = sum_v phi_v`, and the bulk bound `log pi(T) <= F* n + C` follows from a UNIVERSAL
pointwise `phi_v <= F*` off an O(1) boundary.

This module is the exact engine + a BOX-POSITIVITY probe.  It computes the cavity fields, the Bethe A/B terms
(as exact rational log-arguments), and the discharged `phi_v`; and it exposes the EXPONENTIATED inequality
`exp(11 phi_v) <= 621/64` (which clears the `F* = log(621/64)/11` transcendental, leaving an algebraic
statement in the fields `h`) as the target for `worst_corner`/`cone`/`emit_constrained_sos`.  On the extremal
`S(k,5)` fixed point every bulk vertex type saturates (`phi_v = F*`).  The universal discharge (with the
23-adic tie, cf. `docs/BG_23ADIC_RECONCILIATION_20260831.md`) is OPEN.  conjecture1_proved = False.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr

# F* = log(621/64)/11 ; exp(11 F*) = 621/64 (the algebraic target after clearing the transcendental).
F_STAR_ARG = Fr(621, 64)


def _adj(n, edges):
    a = {i: [] for i in range(n)}
    for u, v in edges:
        a[u].append(v)
        a[v].append(u)
    return a


def cavity_fields(n, edges):
    """Exact directed cavity fields `h[(u,v)] = 1/(1 + sum_{c in N(u)\\v} w_{uc} h[(c,u)])` (Fraction, in (0,1])."""
    adj = _adj(n, edges)
    deg = {v: len(adj[v]) for v in range(n)}
    h: dict = {}
    import sys
    sys.setrecursionlimit(1_000_000)

    def H(u, v):
        if (u, v) in h:
            return h[(u, v)]
        s = Fr(0)
        for c in adj[u]:
            if c == v:
                continue
            s += Fr(1, deg[u] * deg[c]) * H(c, u)
        val = Fr(1) / (1 + s)
        h[(u, v)] = val
        return val

    for u, v in edges:
        H(u, v)
        H(v, u)
    return h, deg


def bethe_terms(n, edges):
    """Return `(Aarg, Barg, deg)` where `Aarg[v] = 1 + sum_{u~v} w_{uv} h_{u->v}` (so `A_v = log Aarg[v]`) and
    `Barg[(u,v)] = 1 + w_{uv} h_{u->v} h_{v->u}` (so `B_e = log Barg`), all exact Fractions.  Verified:
    `prod_v Aarg[v] / prod_e Barg[e] == rho(n, edges)` (the exact Bethe product identity)."""
    h, deg = cavity_fields(n, edges)
    adj = _adj(n, edges)
    Aarg = {}
    for v in range(n):
        s = Fr(0)
        for u in adj[v]:
            s += Fr(1, deg[v] * deg[u]) * h[(u, v)]
        Aarg[v] = 1 + s
    Barg = {}
    for u, v in edges:
        Barg[(u, v)] = 1 + Fr(1, deg[u] * deg[v]) * h[(u, v)] * h[(v, u)]
    return Aarg, Barg, deg


def phi_vertices(n, edges, tau):
    """Discharged local free energies `{v: phi_v}` (float) for an edge-discharge `tau(dv, du) -> share in [0,1]`
    of `B_{v,u}` assigned to `v` (the other share `1 - tau(du,dv)` goes to `u`).  `sum_v phi_v == log pi(T)`."""
    Aarg, Barg, deg = bethe_terms(n, edges)
    adj = _adj(n, edges)
    Bof = {}
    for (u, v), b in Barg.items():
        Bof[(u, v)] = b
        Bof[(v, u)] = b
    out = {}
    for v in range(n):
        A = math.log(float(Aarg[v]))
        Bsum = 0.0
        for u in adj[v]:
            Bsum += tau(deg[v], deg[u]) * math.log(float(Bof[(v, u)]))
        out[v] = A - Bsum
    return out, deg


def max_phi(n, edges, tau):
    """`(max_v phi_v, argmax_degree, neighbor_degrees)` under discharge `tau` -- the bulk-bound witness."""
    ph, deg = phi_vertices(n, edges, tau)
    adj = _adj(n, edges)
    best = (-9.9, None, None)
    for v, val in ph.items():
        if val > best[0]:
            best = (val, deg[v], sorted(deg[u] for u in adj[v]))
    return best


# Discharge rules (tau(dv, du) = share of edge B assigned to the degree-dv endpoint).
def tau_equal(dv, du):
    return 0.5


def tau_degree(dv, du):
    """Split proportional to degree (higher degree absorbs more)."""
    return dv / (dv + du)


conjecture1_proved = False
