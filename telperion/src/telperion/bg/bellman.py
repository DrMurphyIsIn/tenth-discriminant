"""Bellman fixed-point instruments — transfer operator + Legendre/large-deviations.

The Brualdi-Goldwasser wall is NOT the recursion (separable, concave) but its
EXTREMAL FIXED POINT: the value function V(m) = sup{logΦ : cavity = m}, a Bellman
fixed point that sits STRICTLY BELOW its own concave hull V̂ in the load-bearing
regime (so it has no concave and no closed form), with V(tie) = 0 an arithmetic
coincidence.  Two of the three missing tools have NO finite certificate; what
Telperion CAN provide is the exact-arithmetic INSTRUMENTATION to probe them:

  1. TRANSFER OPERATOR: compute the extremal fixed point V exactly on a grid and
     the sub-hull gap V̂ − V (the object with no usable upper bound); track the
     spectral ratio R(s+1)/R(s) whose crossing of 1 is the tie.

  2. LEGENDRE / LARGE-DEVIATIONS: the Bellman step is a sup-convolution
     (sup Σ V(mᵢ) at fixed Σmᵢ = r·V̂(S/r)); the concave hull IS the biconjugate
     V** (double Legendre), and V̂ − V measures which configurations realize the
     hull (rate 0) vs fall below it (rate > 0) -- the Cramér structure.

These are checkers/instruments, not emitters: a future proof supplies the tight
bound on V̂ − V; these compute it exactly so a candidate can be tested.
"""
from __future__ import annotations

import itertools
import math
from fractions import Fraction as Fr


def _phi11(cr, kids):
    ch = [_phi11(*k) for k in kids]
    S = sum(m for m, _ in ch)
    d = len(kids) + 1 + cr
    z = Fr(3, 3 * d + cr)
    m = z / (1 + z * S)
    a11 = (Fr(3, 2) ** (11 * cr)) * (1 + Fr(cr, 3 * d)) ** 11 * (Fr(64, 621) ** (1 + 2 * cr))
    p = a11 * (1 + z * S) ** 11
    for _, q in ch:
        p *= q
    return (m, p)


def value_function(max_size: int = 16, max_trees: int = 4000) -> dict:
    """The extremal fixed point V(m) = sup logΦ at cavity m, computed exactly (as
    max Φ¹¹ per cavity, logΦ = log(Φ¹¹)/11) over a bounded tree enumeration.
    Returns {float(cavity): (V, exact_phi11)}."""
    base = [(c, []) for c in range(0, 7)]
    pool, allT = list(base), list(base)
    stop = False
    for _ in range(3):
        newp = []
        for cr in range(0, 6):
            for r in range(1, 4):
                for combo in itertools.combinations_with_replacement(pool, r):
                    T = (cr, list(combo))
                    if _size(T) <= max_size:
                        allT.append(T)
                        newp.append(T)
                        # Enforce the ``max_trees`` budget DURING enumeration, not
                        # only after each outer sweep.  ``pool`` grows every sweep
                        # (~1881 after sweep 1), so ``combinations_with_replacement
                        # (pool, 3)`` reaches ~1e9 tuples and the old post-sweep
                        # check at the loop tail never fires -- the hang.  Breaking
                        # as soon as the budget is reached bounds the work.
                        if len(allT) > max_trees:
                            stop = True
                            break
                if stop:
                    break
            if stop:
                break
        pool = base + newp
        if stop:
            break
    allT = list({repr(T): T for T in allT}.values())
    U = {}
    for T in allT:
        m, p = _phi11(*T)
        if m not in U or p > U[m]:
            U[m] = p
    return {float(m): (math.log(float(p)) / 11, p) for m, p in U.items()}


def _size(T):
    cr, kids = T
    return 1 + 2 * cr + sum(_size(k) for k in kids)


def concave_hull(points: list[tuple[float, float]]) -> list[tuple[float, float]]:
    """Upper concave hull of (x, y) points — the biconjugate V** (double Legendre
    transform), computed by an Andrew-monotone-chain upper hull."""
    pts = sorted(set(points))
    if len(pts) < 3:
        return pts
    hull = []
    for p in pts:
        while len(hull) >= 2 and _cross(hull[-2], hull[-1], p) >= 0:
            hull.pop()
        hull.append(p)
    return hull


def _cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def sub_hull_gap(V: dict) -> tuple[float, float]:
    """max_m (V̂(m) − V(m)) and the argmax — the sub-hull gap with no usable upper
    bound (the object tool #1 must control).  V̂ is the concave hull of V."""
    pts = [(x, v) for x, (v, _) in V.items()]
    hull = concave_hull(pts)
    hx = [p[0] for p in hull]
    hy = [p[1] for p in hull]
    worst = (0.0, None)
    for x, (v, _) in V.items():
        vhat = _interp(hx, hy, x)
        if vhat - v > worst[0]:
            worst = (vhat - v, x)
    return worst


def _interp(xs, ys, x):
    if x <= xs[0]:
        return ys[0]
    if x >= xs[-1]:
        return ys[-1]
    for i in range(len(xs) - 1):
        if xs[i] <= x <= xs[i + 1]:
            t = (x - xs[i]) / (xs[i + 1] - xs[i])
            return ys[i] * (1 - t) + ys[i + 1] * t
    return ys[-1]


def fenchel_transform(points: list[tuple[float, float]], slopes) -> list[tuple[float, float]]:
    """The Legendre-Fenchel transform V*(p) = sup_x (p·x − V(x)) on sampled
    slopes — the dual of the sup-convolution Bellman step.  (Concave version:
    inf_x (p·x − V(x)) for the upper transform; we use the sup for the convex
    conjugate of −V.)"""
    out = []
    for p in slopes:
        out.append((p, max(p * x - v for x, v in points)))
    return out


def cramer_rate(V: dict) -> dict:
    """The large-deviations rate at each cavity: I(m) = V̂(m) − V(m) >= 0, zero on
    the configurations that REALIZE the concave hull and positive on those that
    fall strictly below it (the discrete class-curves not filling their hull) --
    the Cramér structure of why V < V̂."""
    pts = [(x, v) for x, (v, _) in V.items()]
    hull = concave_hull(pts)
    hx = [p[0] for p in hull]
    hy = [p[1] for p in hull]
    return {x: max(0.0, _interp(hx, hy, x) - v) for x, (v, _) in V.items()}
