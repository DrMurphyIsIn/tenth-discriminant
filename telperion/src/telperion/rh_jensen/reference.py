# src/telperion/rh_jensen/reference.py
"""High-precision mpmath ORACLE for Riemann-xi Taylor coefficients.

Test/reference use ONLY. Never import from certificate/emitter code paths.
conjecture1_proved = False.

The Riemann xi function is:
    xi(s) = 1/2 * s*(s-1) * pi^{-s/2} * Gamma(s/2) * zeta(s)

The completed Xi function on the critical line is:
    Xi(t) = xi(1/2 + i*t)

Xi is real-valued (by the functional equation xi(s) = xi(1-s)) and even in t.
Its Taylor expansion at t=0 is:
    Xi(t) = sum_{m >= 0} alpha(m) * t^{2m}

where alpha(m) is the coefficient of t^{2m}.  In particular:
    alpha(0) = Xi(0) = xi(1/2)
"""
import mpmath


def _xi(s: mpmath.mpf) -> mpmath.mpf:
    """Riemann completed xi function: xi(s) = 1/2 * s*(s-1) * pi^{-s/2} * Gamma(s/2) * zeta(s)."""
    return mpmath.mpf("0.5") * s * (s - 1) * mpmath.power(mpmath.pi, -s / 2) \
        * mpmath.gamma(s / 2) * mpmath.zeta(s)


def xi_at_zero_reference(prec_bits: int = 400) -> mpmath.mpf:
    """Return xi(1/2) computed directly from zeta, Gamma, pi at high precision.

    This is the anchor value: Xi(0) = xi(1/2) ~ 0.49712077818831411.
    """
    old = mpmath.mp.prec
    try:
        mpmath.mp.prec = prec_bits
        return mpmath.re(_xi(mpmath.mpf("0.5")))
    finally:
        mpmath.mp.prec = old


def xi_coeff_reference(m: int, prec_bits: int = 400) -> mpmath.mpf:
    """Return the normalized xi Maclaurin coefficient alpha(m).

    Xi(t) = xi(1/2 + i*t) = sum_{m >= 0} alpha(m) * t^{2m}

    alpha(m) is the coefficient of t^{2m} in the Taylor expansion of Xi at t=0.
    Xi is an even real function of t, so all odd-degree coefficients vanish.

    Uses mpmath.taylor on the real even function t -> Re(xi(1/2 + i*t)).
    """
    old = mpmath.mp.prec
    try:
        mpmath.mp.prec = prec_bits

        def f(t):
            return mpmath.re(_xi(mpmath.mpf("0.5") + 1j * t))

        coeffs = mpmath.taylor(f, 0, 2 * m + 2)
        return coeffs[2 * m]
    finally:
        mpmath.mp.prec = old
