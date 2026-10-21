"""Rigorous rational enclosures of the Li–Keiper coefficients (li_positivity backend).

conjecture1_proved = False.  This module does NOT prove RH.  It produces
certified rational boxes for

    taylorCoeff riemannXi n     (upstream ``LiChallenge``/``LiCriterion`` convention)
        = the n-th Maclaurin coefficient of  z ↦ (d/dz) log ξ(1/(1−z))
        = Li's classical λ_{n+1}

which the ``LiPositivityLadderEmitter`` rungs are instantiated at.

Series route (no pole ever appears)
-----------------------------------
With ``u(z) = 1/(1−z)`` the map sends ``z = 0 → s = 1``, where ζ has its pole.
We never expand there: by the functional equation ``ξ(s) = ξ(1−s)``,

    F(z) := ξ(1/(1−z)) = ξ(1 + w) = ξ(−w),      w = z/(1−z),

so with ``g(z) = −z/(1−z)`` (constant term 0) we need ξ expanded at 0.  There
the completed form

    ξ(s) = (s−1) · π^{−s/2} · Γ(s/2 + 1) · ζ(s)

is analytic factor-by-factor: ``s·Γ(s/2)`` has been absorbed into the entire
``Γ(s/2+1)`` (value 1 at 0) and ζ is analytic at 0 (ζ(0) = −1/2).  Every factor
is an ``acb_series`` primitive (``exp``/``log``/``gamma``/``zeta``), applied to
the series ``g`` directly — flint composes through the function, so no manual
series composition is needed.  Then

    taylorCoeff n = [z^n] F′(z)/F(z),           F(0) = ξ(1) = 1/2 ≠ 0,

read off ``xi.derivative() * xi.inv()``.

Rigor argument
--------------
Identical to ``rh_jensen.coefficients`` (see its module docstring): Arb ball
arithmetic guarantees every coefficient ball contains the true value; exact
OUTWARD dyadic endpoints are recovered via ``man_exp()`` so the returned
``fractions.Fraction`` pair is a rigorous enclosure.  Raising ``prec_bits``
narrows it.  Truncating the series at ``cap`` does not perturb lower-order
coefficients (truncated power-series arithmetic is exact on the retained
prefix).

Generation-time self-check: the first three enclosures must contain the
PUBLISHED Li–Keiper values (Keiper 1992 / Li 1997 / Coffey 2004) — an external
anchor; a normalization or index-shift bug aborts here rather than emitting.

This coefficient-membership fact (λ ∈ [lo, hi]) is the ladder's ONE documented
non-kernel input, carried into Lean as the rung hypothesis ``hlo``.

Dependency: python-flint (Arb/FLINT).
"""
from __future__ import annotations

from fractions import Fraction

from .rh_jensen.coefficients import _arb_ball_to_fractions

# Published 7-digit truncations of λ₁, λ₂, λ₃ (indices n = 0, 1, 2) with slack.
_PUBLISHED_ANCHORS = {
    0: Fraction("0.0230957"),
    1: Fraction("0.0923457"),
    2: Fraction("0.2076389"),
}
_ANCHOR_SLACK = Fraction(1, 10**6)


def enclose_li_coeffs(count: int, prec_bits: int = 256) -> list[tuple[Fraction, Fraction]]:
    """Rigorous outward enclosures of ``taylorCoeff riemannXi n`` for n < count.

    One series computation yields the whole prefix.  Raises ``ValueError`` if
    the published-value self-check fails (normalization/index bug) — refusal,
    never a wrong box.
    """
    from flint import acb, acb_series, ctx

    if count <= 0:
        raise ValueError(f"enclose_li_coeffs: need count >= 1, got {count}")

    old_prec, old_cap = ctx.prec, ctx.cap
    try:
        ctx.prec = prec_bits
        ctx.cap = count + 1  # logDeriv consumes one derivative order

        z = acb_series([0, 1])
        one = acb_series([1])
        g = -z * (one - z).inv()                     # −z/(1−z), constant term 0
        pi_log = acb.pi().log()
        xi = ((g - one)
              * (-(g / 2) * pi_log).exp()           # π^{−s/2} at s = g
              * (g / 2 + one).gamma()               # Γ(s/2 + 1)
              * g.zeta())                           # ζ(s), analytic at 0
        logderiv = xi.derivative() * xi.inv()        # F′/F, F(0) = 1/2

        coeffs = logderiv.coeffs()[:count]
    finally:
        ctx.prec, ctx.cap = old_prec, old_cap

    boxes = [_arb_ball_to_fractions(c.real) for c in coeffs]

    for n, anchor in _PUBLISHED_ANCHORS.items():
        if n < count:
            lo, hi = boxes[n]
            if not (lo - _ANCHOR_SLACK <= anchor <= hi + _ANCHOR_SLACK):
                raise ValueError(
                    f"li_coeff SELF-CHECK FAILED at n={n}: enclosure "
                    f"[{float(lo)}, {float(hi)}] does not contain the published "
                    f"Li–Keiper value {float(anchor)} — normalization or index "
                    f"convention broke; refusing to hand out boxes")
    return boxes


def enclose_li_coeff(n: int, prec_bits: int = 256) -> tuple[Fraction, Fraction]:
    """Single-coefficient convenience wrapper over :func:`enclose_li_coeffs`."""
    if n < 0:
        raise ValueError(f"enclose_li_coeff: need n >= 0, got {n}")
    return enclose_li_coeffs(n + 1, prec_bits=prec_bits)[n]
