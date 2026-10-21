# src/telperion/rh_jensen/coefficients.py
"""Rigorous rational enclosures of the Riemann-xi Taylor coefficients alpha(m).

conjecture1_proved = False. This module does NOT prove RH. It produces certified
rational boxes for the concrete Maclaurin coefficients of

    Xi(t) = xi(1/2 + i*t) = sum_{m >= 0} alpha(m) * t^{2m}

(the same xi and normalization as telperion.rh_jensen.reference), which later Lean
theorems are instantiated at.

Rigor argument
--------------
The enclosure is computed with the Arb library (via python-flint's ``acb``/
``acb_series``). Arb implements *ball arithmetic*: every intermediate value is a
ball ``[midpoint +/- radius]`` that is GUARANTEED to contain the true value, with
the radius propagating a rigorous, directed-rounded error bound through every
operation (multiplication, ``exp``, ``gamma``, ``zeta``, and power-series
composition included). We form the entire xi expression as a truncated power
series in ``t`` about ``t = 0``; the coefficient of ``t^k`` is then an ``acb``
ball, and its ``.real`` part is an ``arb`` ball that rigorously encloses alpha(k)
(k = 2m for the even coefficients; odd coefficients vanish).

We extract EXACT rational OUTWARD endpoints from that ball:

  * ``ball.mid()`` is the exact dyadic midpoint (its own radius is zero); we read
    its exact mantissa/exponent via ``man_exp()`` -> ``man * 2**exp``.
  * ``ball.rad()`` returns an ``arb`` that is a certified UPPER BOUND of the true
    radius; we read its exact dyadic value the same way. Because it upper-bounds
    the radius, ``[mid - rad, mid + rad]`` still contains the true alpha(m).
  * lo = Fraction(mid) - Fraction(rad); hi = Fraction(mid) + Fraction(rad).

All endpoints are exact ``fractions.Fraction`` (no float). Since the true value
lies in ``[mid - true_rad, mid + true_rad]`` and ``rad >= true_rad``, the returned
``(lo, hi)`` is a rigorous enclosure. Raising ``prec_bits`` shrinks the Arb ball
radii, so the returned interval narrows.

This coefficient-membership fact (alpha(m) in [lo, hi]) is the plan's ONE
documented non-kernel input: it is certified by Arb ball arithmetic (python-flint),
not by the Lean kernel. Everything downstream of the rational box IS kernel-checked.

Dependency: python-flint (Arb/FLINT). See pyproject.toml.
"""
from fractions import Fraction

from flint import acb, acb_series, ctx


def _arb_ball_to_fractions(ball) -> tuple[Fraction, Fraction]:
    """Convert an arb ball [mid +/- rad] to exact OUTWARD rational (lo, hi).

    ``ball.mid()`` is exact (radius 0); ``ball.rad()`` is a certified upper bound
    of the true radius. Both are dyadic rationals recovered exactly via man_exp().
    """
    mid = ball.mid()
    rad = ball.rad()

    def _dyadic(a) -> Fraction:
        man, exp = a.man_exp()
        man = int(man)
        exp = int(exp)
        if exp >= 0:
            return Fraction(man) * (Fraction(2) ** exp)
        return Fraction(man, 2 ** (-exp))

    mid_f = _dyadic(mid)
    rad_f = _dyadic(rad)
    # rad_f >= true radius (Arb guarantees .rad() upper-bounds the ball radius),
    # so widening by rad_f in both directions keeps the true value enclosed.
    return (mid_f - rad_f, mid_f + rad_f)


def _xi_series_coeffs(max_index: int, prec_bits: int) -> list:
    """Return the list of acb power-series coefficients of Xi(t) about t = 0.

    Xi(t) = xi(1/2 + i*t) with
        xi(s) = 1/2 * s*(s-1) * pi^{-s/2} * Gamma(s/2) * zeta(s).

    Coefficient index k corresponds to the t^k term. ``max_index`` is the highest
    index that must be available (so we request series length max_index + 1).
    """
    length = max_index + 1
    old_prec = ctx.prec
    try:
        ctx.prec = prec_bits
        # s(t) = 1/2 + i*t as a power series in t, truncated to `length` terms.
        s = acb_series([acb("0.5"), acb(0, 1)], length)
        pi = acb.pi()
        # pi^{-s/2} = exp(-s/2 * log(pi)); log(pi) is a constant series.
        log_pi = acb_series([acb.log(pi)], length)
        pi_pow = (log_pi * (-s / 2)).exp()
        xi = acb("0.5") * s * (s - 1) * pi_pow * (s / 2).gamma() * s.zeta()
        return list(xi)
    finally:
        ctx.prec = old_prec


def enclose_xi_coeff(m: int, prec_bits: int) -> tuple[Fraction, Fraction]:
    """Rigorous rational enclosure (lo, hi) of alpha(m) with lo <= alpha(m) <= hi.

    alpha(m) is the coefficient of t^{2m} in Xi(t) = xi(1/2 + i*t) (real, even).
    Endpoints are exact fractions.Fraction, rounded OUTWARD. Higher prec_bits gives
    a narrower interval.
    """
    if m < 0:
        raise ValueError("m must be >= 0")
    idx = 2 * m
    coeffs = _xi_series_coeffs(idx, prec_bits)
    real_ball = coeffs[idx].real
    return _arb_ball_to_fractions(real_ball)


def enclose_coeff_box(n: int, d: int, prec_bits: int) -> list[tuple[Fraction, Fraction]]:
    """Return enclosures for alpha(n), alpha(n+1), ..., alpha(n+d).

    Uses ONLY the rigorous acb_series path (direct power-series ball arithmetic).
    python-flint's acb_series zeta implementation returns at most 10 terms
    (indices 0..9), so alpha(m) for m >= 5 (index 2m >= 10) is inaccessible
    via this path. Any requested coefficient with 2k > 9 raises
    NotImplementedError -- it must NOT be produced by a non-series extraction
    method that lacks a rigorous truncation-tail bound (see the DEFERRED note in
    docs/JENSEN_HYPERBOLICITY_STATUS.md). Rigorous high-m coefficients require a
    Cauchy tail bound |alpha(k)| <= max_{|t|=R}|Xi(t)| / R^{2k} and are deferred
    to Phase 2.

    conjecture1_proved = False. This function does NOT prove RH.
    """
    if n < 0 or d < 0:
        raise ValueError("n and d must be >= 0")

    result: list[tuple[Fraction, Fraction]] = []
    for k in range(n, n + d + 1):
        if 2 * k <= 9:
            result.append(enclose_xi_coeff(k, prec_bits))
        else:
            raise NotImplementedError(
                f"enclose_coeff_box: alpha({k}) needs series index {2*k} > 9, "
                "outside python-flint's acb_series zeta range (10 terms). "
                "Rigorous alpha(m) for m >= 5 requires a Cauchy truncation-tail "
                "bound and is DEFERRED to Phase 2. Do NOT substitute a "
                "finite-evaluation extraction that drops the tail (unsound)."
            )

    return result
