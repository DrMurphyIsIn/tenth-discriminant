# src/telperion/rh_jensen/jensen.py
"""Jensen polynomial assembly and d=2 Turan discriminant margin.

conjecture1_proved = False. This module does NOT prove RH. It assembles the
Jensen polynomial coefficient boxes from the Riemann-xi Taylor coefficient
enclosures, and certifies a rational lower bound on the d=2 discriminant
  D(c) = c_1^2 - 4 * c_0 * c_2
over a rational box. This is the discriminant b^2 - 4ac of the quadratic Jensen
polynomial a*X^2 + b*X + c with a = c_2, b = c_1, c = c_0. A positive lower
bound certifies real-rootedness (and thus log-concavity) for every polynomial
in the box.

Definitions
-----------
Given n >= 0, d >= 0, the degree-d Jensen polynomial at offset n is
    J_{n,d}(x) = sum_{k=0}^{d} C(d,k) * alpha(n+k) * x^k
where alpha(m) is the coefficient of t^{2m} in Xi(t) = xi(1/2 + i*t) and
C(d,k) = math.comb(d, k) is the exact binomial coefficient. The Jensen
coefficients are c_k = C(d,k) * alpha(n+k).

Rigor
-----
All computations use exact fractions.Fraction; no float arithmetic enters.
The coefficient boxes from enclose_coeff_box are rigorous (see coefficients.py).
Scaling by the exact positive integer C(d,k) preserves the enclosure exactly.
The disc2_margin function computes a rigorous rational LOWER bound of the true
discriminant D(c) = c_1^2 - 4*c_0*c_2 over the box using signed interval
arithmetic. This is the discriminant b^2 - 4ac of the quadratic Jensen
polynomial a*X^2 + b*X + c with a = c_2, b = c_1, c = c_0
(J_{n,2}(X) = alpha(n) + 2*alpha(n+1)*X + alpha(n+2)*X^2). D(c) >= 0 is exactly
the real-rootedness criterion for that quadratic.

    lower(c_1^2) - 4 * upper(c_0 * c_2)

where:
  - lower(c_1^2): if the interval [lo1, hi1] straddles zero (lo1 <= 0 <= hi1),
    the minimum square is 0; otherwise it is min(lo1^2, hi1^2) (the endpoint
    closest to zero, squared).
  - upper(c_0 * c_2): the maximum over all four endpoint products
    max(lo0*lo2, lo0*hi2, hi0*lo2, hi0*hi2).

Both bounds are attained at the box endpoints, so the bound is tight and exact.
"""

import math
from fractions import Fraction

from telperion.rh_jensen.coefficients import enclose_coeff_box


def jensen_coeff_box(
    n: int, d: int, prec_bits: int
) -> list[tuple[Fraction, Fraction]]:
    """Return the box for Jensen polynomial coefficients c_k = C(d,k)*alpha(n+k).

    Parameters
    ----------
    n : int >= 0
        Starting index into the alpha sequence.
    d : int >= 0
        Degree; the box has d+1 entries indexed k=0..d.
    prec_bits : int
        Precision bits passed to the Arb coefficient enclosure.

    Returns
    -------
    list of (lo, hi) pairs as exact fractions.Fraction, length d+1.
    Each pair is a rigorous enclosure: lo <= c_k <= hi.
    """
    if n < 0:
        raise ValueError("n must be >= 0")
    if d < 0:
        raise ValueError("d must be >= 0")

    alpha_box = enclose_coeff_box(n, d, prec_bits)  # length d+1, alpha(n+k) enclosures

    result: list[tuple[Fraction, Fraction]] = []
    for k in range(d + 1):
        w = math.comb(d, k)  # exact positive integer
        lo_alpha, hi_alpha = alpha_box[k]
        # Scaling [lo, hi] by a positive integer w: [w*lo, w*hi] is exact.
        result.append((Fraction(w) * lo_alpha, Fraction(w) * hi_alpha))

    return result


def disc2_margin(box: list[tuple[Fraction, Fraction]]) -> Fraction:
    """Rigorous rational lower bound on the d=2 discriminant D(c) = c_1^2 - 4*c_0*c_2.

    This is the discriminant b^2 - 4ac of the quadratic Jensen polynomial
    a*X^2 + b*X + c with a = c_2, b = c_1, c = c_0.

    Computes:
        lower(c_1^2) - 4 * upper(c_0 * c_2)

    where both extrema are taken over ALL c in the box. A positive return value
    certifies that every polynomial in the box has D(c) > 0, i.e., is real-rooted.

    Parameters
    ----------
    box : list of 3 (lo, hi) pairs as exact fractions.Fraction
        box[k] = (lo_k, hi_k) rigorous enclosure of c_k, k=0,1,2.

    Returns
    -------
    Fraction: a certified rational lower bound on min_{c in box} D(c).
    """
    if len(box) != 3:
        raise ValueError(f"disc2_margin requires a box of length 3, got {len(box)}")

    lo0, hi0 = box[0]
    lo1, hi1 = box[1]
    lo2, hi2 = box[2]

    # --- lower bound of c_1^2 over [lo1, hi1] ---
    # c_1^2 is a convex function. Its minimum over [lo1, hi1] is:
    #   0          if the interval straddles zero (lo1 <= 0 <= hi1)
    #   min(lo1^2, hi1^2) otherwise (the nearer endpoint to zero, squared)
    if lo1 <= Fraction(0) <= hi1:
        c1_sq_lower = Fraction(0)
    else:
        c1_sq_lower = min(lo1 * lo1, hi1 * hi1)

    # --- upper bound of c_0 * c_2 over [lo0, hi0] x [lo2, hi2] ---
    # The product of two interval variables achieves its extremes at the
    # four corners; we take the max.
    c0c2_upper = max(
        lo0 * lo2,
        lo0 * hi2,
        hi0 * lo2,
        hi0 * hi2,
    )

    return c1_sq_lower - Fraction(4) * c0c2_upper
