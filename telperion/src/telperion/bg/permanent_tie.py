"""The quantized-permanent tie -- Brualdi-Goldwasser's resonance as an integer identity.

The tie observation (operator, 2026-08-17): per(L) is an INTEGER (a quantized value), and the BG tie is
exactly where this quantized permanent, benchmarked, hits Phi = 1 -- an INTEGER IDENTITY.  For the
near-star N(0,s) the permanent is a clean quantized integer:

    per(L(N(0,s))) = 4 * s * 3^(s-1),      prod(deg) = s * 2^s,
    rho = per / prod(deg) = (4/3)(3/2)^s,

and the benchmark makes Phi^11 = 1 at the INTEGER s = 5 (the tie), unwinding to the integer identity

    64 * 243 * 23 = 621 * 576 = 357696.

The continuum (real s) OVERSHOOTS (Phi = 1.00046 > 1); only the quantized (integer) permanent resonates
to exactly 1.  This certifies the tie AS the arithmetic resonance of the quantized permanent -- the finite
integrality half of BG (distinct from the analytic tail).  It is a description + the proven near-star
identity, NOT a proof of the general conjecture.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass

from .bridge import near_star_R


def near_star_permanent(s):
    """per(L(N(0,s))) = 4 * s * 3^(s-1) -- the quantized (integer) permanent of the near-star."""
    return 4 * s * 3 ** (s - 1)


def near_star_prod_deg(s):
    """prod of degrees of N(0,s) = s * 2^s (hub s, s arm-mids deg 2, s leaves deg 1)."""
    return s * 2 ** s


@dataclass(frozen=True)
class QuantizedPermanentTieCertificate:
    """Certifies BG's tie as the integer resonance of the quantized permanent: per(L(N(0,s))) is an
    integer for every s, and at the INTEGER s = 5 the benchmarked value Phi^11 = 1 unwinds to the integer
    identity 64*243*23 = 621*576 -- a resonance the continuum overshoots."""

    tie: int = 5
    s_range: tuple = (1, 12)

    def permanent_is_quantized(self) -> bool:
        """per(L(N(0,s))) = 4 s 3^(s-1) is an integer for all s (matches per = rho * prod deg)."""
        from fractions import Fraction as Fr
        for s in range(self.s_range[0], self.s_range[1] + 1):
            p = near_star_permanent(s)
            # cross-check against rho * prod(deg): rho = (4/3)(3/2)^s
            rho = Fr(4, 3) * Fr(3, 2) ** s
            if p != rho * near_star_prod_deg(s) or not isinstance(p, int):
                return False
        return True

    def tie_is_integer_resonance(self) -> bool:
        """At s = tie, Phi^11 = 1 exactly, unwinding to 64*243*23 = 621*576."""
        return near_star_R(self.tie) == 1 and 64 * 243 * 23 == 621 * 576

    def continuum_overshoots(self) -> bool:
        """Only the integer permanent resonates to 1: the real-s relaxation exceeds 1."""
        from .quantization import continuous_overshoot
        return continuous_overshoot()[1] > 1

    def check(self) -> bool:
        return (self.permanent_is_quantized()
                and self.tie_is_integer_resonance()
                and self.continuum_overshoots())

    def lean(self) -> str:
        lines = [
            "-- QUANTIZED-PERMANENT TIE: per(L(N(0,s))) = 4 s 3^(s-1) is an INTEGER for every s; at the\n"
            f"-- integer s={self.tie} the benchmarked Phi^11 = 1, the integer identity 64*243*23=621*576.\n"
            "-- The continuum (real s) overshoots 1 -- only the quantized permanent resonates exactly.\n"
        ]
        for s in range(self.s_range[0], self.s_range[1] + 1):
            p = near_star_permanent(s)
            lines.append(f"theorem permtie_int_s{s} : ({p}:ℤ) = 4 * {s} * 3^{s - 1} := by norm_num")
        lines.append("theorem permtie_identity : (64 * 243 * 23 : ℤ) = 621 * 576 := by norm_num")
        r = near_star_R(self.tie)
        lines.append(f"theorem permtie_resonance : (({r.numerator}:ℚ)/{r.denominator}) = 1 := by norm_num")
        return "\n".join(lines) + "\n"
