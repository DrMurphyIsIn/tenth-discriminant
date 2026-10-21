"""Ehrhart / quasi-polynomial instruments — the moonshot that would EXPLAIN the 23.

Avenue D: every other method VERIFIES the modulus 23 (from cavity m = 3/23,
ρ_B^11 = 621/64 = 3^3·23 / 2^6).  If the gap D − N (for Φ^11 = N/D) is a SIGNED
LATTICE-POINT COUNT, then 23 is an Ehrhart QUASI-POLYNOMIAL PERIOD -- making the
integrality structural rather than a coincidence.  This is the only avenue that
would tell us WHY 23, not merely verify 23.

Exact-engine instruments (no finite certificate -- lattice-point/toric machinery
is a research build): fit a sequence to a quasi-polynomial of a given period
(each residue class mod p is a polynomial of bounded degree) and, crucially,
PROBE whether the crux's D − N along a scaling family exhibits period 23.  A
positive result would turn the arithmetic tie from obstacle into theorem.
"""
from __future__ import annotations

from fractions import Fraction as Fr


def fit_polynomial(xs, ys, deg: int):
    """Exact least-degree interpolating polynomial coefficients (rational) for
    points (xs, ys) if they lie on a degree-≤deg polynomial, else None."""
    if len(xs) < deg + 1:
        return None
    # solve Vandermonde on the first deg+1 points, then verify the rest
    import sympy as sp
    a = sp.symbols(f"a0:{deg+1}")
    def val(x):
        return sum(a[k] * Fr(x) ** k for k in range(deg + 1))
    sol = sp.solve([val(xs[i]) - Fr(ys[i]) for i in range(deg + 1)], a, dict=True)
    if not sol:
        return None
    coeffs = [sol[0][a[k]] for k in range(deg + 1)]
    for i in range(len(xs)):
        if sum(coeffs[k] * Fr(xs[i]) ** k for k in range(deg + 1)) != Fr(ys[i]):
            return None
    return coeffs


def is_quasi_polynomial(seq, period: int, max_deg: int = 3) -> bool:
    """True iff `seq` (indexed 0,1,2,...) is a quasi-polynomial of the given
    period: each residue class r mod period lies on one polynomial of degree
    ≤ max_deg.  Period p being minimal is the Ehrhart period."""
    seq = list(seq)
    for r in range(period):
        idx = list(range(r, len(seq), period))
        if len(idx) < 2:
            continue
        xs = [i for i in idx]
        ys = [seq[i] for i in idx]
        ok = any(fit_polynomial(xs, ys, d) is not None
                 for d in range(min(max_deg, len(xs) - 1) + 1))
        if not ok:
            return False
    return True


def minimal_period(seq, candidates, max_deg: int = 3):
    """The smallest period in `candidates` for which `seq` is quasi-polynomial --
    the Ehrhart period, if one exists.  For the crux probe: does D − N have
    period 23?"""
    for p in sorted(candidates):
        if is_quasi_polynomial(seq, p, max_deg):
            return p
    return None
