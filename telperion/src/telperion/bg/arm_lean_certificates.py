"""Lean-tight formalization of R1's two scalar inequalities (single-hub arm-extremality).

R1 proved the single-hub arm-extremality theorem (`Phi^11(B) <= 486/529` for large-message blocks, arm the
unique max) modulo formalizing two finite-margin scalar inequalities.  This module pins those two to
KERNEL-CHECKABLE form, validates them in exact `Fraction` arithmetic (the telperion green gate), and carries
the Lean theorem statements emitted to `examples/g1_floors/lean/ArmExtremality.lean` (namespace `G1.ArmExtremality`).

Trust model (telperion METHODOLOGY): nothing is formalized before it is validated in exact arithmetic; the
Lean kernel then re-proves it from scratch, so a generator bug is a compile failure, never a false theorem.

--- INEQUALITY 1 (the L1 scalar): B(L,j') <= (3/2)^11 -------------------------------------------------------
`B(L,j') = W^L * [(3j'+L+3)/(2j'+2)]^11`, `W = 64/621`, over integers `0 <= L <= j'`.  Two facts close it:

  * BASE (equality at L=0): `B(0,j') = [3(j'+1)/(2(j'+1))]^11 = (3/2)^11` for every `j'` (cancel `j'+1 > 0`).
  * DESCENT: `B` is strictly decreasing in `L` (for `j' >= 1`), because the per-step ratio
    `B(L,j')/B(L-1,j') = W*[(m+1)/m]^11 <= 1` with `m = 3j'+L+2 >= 6`.  That reduces to the INTEGER TAIL

        64*(m+1)^11 <= 621*m^11   for every integer m >= 6   (tightest at m=6; FALSE at m=4).

    Kernel-tight via the all-nonnegative-coefficient Polya identity (`m = 6+k`):
        621*(6+k)^11 = 64*(7+k)^11 + P(k),   P(k) a degree-11 polynomial with all coefficients >= 0,
    so `64*(7+k)^11 <= 621*(6+k)^11` by `Nat.le_add_right`.  Hence `B(L,j') <= (3/2)^11`, equality iff L=0.

--- INEQUALITY 2 (the j=2 closure): the g-step, and its final rational certificate ------------------------
The j=2 case bounds `Phi^11(B) <= W*g(C1)*g(C2)` (exact AM-GM split) with `g(C) = Phi^11(C)*(1+mu_C/3)^11`,
and the g-lemma gives `g(C) <= gamma := W^2*(5/3)^11` for every non-leaf block.  The FINAL algebra is a single
EXACT RATIONAL certificate, kernel-checkable directly:

        W*gamma^2 = W^5*(5/3)^22 < 486/529    <=>    W^3*(50/27)^11 < 1    <=>    64^3*50^11 < 621^3*27^11.

HONEST RESIDUAL (what is NOT yet symbolic).  The g-lemma's inductive step is a genuine MULTI-VARIABLE
optimization: `max over child messages of W*[1+(3S'+1)/(3j'+3)]^11 * prod_i min(1, gamma/(1+mu_i/3)^11) < gamma`.
Crude separable bounds give `~8.9 > gamma`, so the two-regime product is load-bearing (collective cancellation)
-- it is NOT a simple Polya scalar.  It is grid-verified (`< gamma`), not symbolically proved; a faithful
reconstruction here maxes at `~2.552 < gamma = 2.928` (interior; the R1 write-up reports `2.538`, same
conclusion, small formulation difference).  So this module Lean-tightens the CLEAN halves -- Inequality 1 in
full and Inequality 2's final rational certificate -- and names the g-step optimization as the remaining
symbolic residual.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

W = Fr(64, 621)
GAMMA = W ** 2 * Fr(5, 3) ** 11
F_ARM = Fr(486, 529)
THREE_HALVES_11 = Fr(3, 2) ** 11

# P(k) coefficients (degree 11 down to 0) of  621*(6+k)^11 - 64*(7+k)^11  -- all nonnegative (the Polya witness).
TAIL_P_COEFFS = (
    557, 36058, 1057100, 18510360, 214880160, 1734000576,
    9907054080, 39974056320, 111225554880, 202159010240, 214181872960, 98748060224,
)


def B(L: int, jp: int) -> Fr:
    """`B(L,j') = W^L * [(3j'+L+3)/(2j'+2)]^11`."""
    return W ** L * Fr(3 * jp + L + 3, 2 * jp + 2) ** 11


def tail_identity_holds(k: int) -> bool:
    """The Polya identity `621*(6+k)^11 = 64*(7+k)^11 + P(k)` at a given `k`."""
    P = sum(c * k ** (11 - i) for i, c in enumerate(TAIL_P_COEFFS))
    return 621 * (6 + k) ** 11 == 64 * (7 + k) ** 11 + P


def per_step_holds(m: int) -> bool:
    """The integer tail `64*(m+1)^11 <= 621*m^11`."""
    return 64 * (m + 1) ** 11 <= 621 * m ** 11


def final_rational_certificate() -> bool:
    """`64^3*50^11 < 621^3*27^11`  (<=>  `W^3*(50/27)^11 < 1`  <=>  `W*gamma^2 < 486/529`)."""
    return 64 ** 3 * 50 ** 11 < 621 ** 3 * 27 ** 11


@dataclass(frozen=True)
class ArmLeanCertificate:
    """Lean-tight formalization of R1's two scalar inequalities.  `check()` validates, in exact arithmetic:
    the all-nonneg-coefficient Polya tail identity, the integer per-step tail (`m >= 6`, tight at 6, false at
    4), the base equality `B(0,j')=(3/2)^11`, the descent `B(L,j') <= (3/2)^11`, and the j=2 final rational
    certificate `64^3*50^11 < 621^3*27^11`.  These are the green gate for the emitted Lean (namespace
    `G1.ArmExtremality`).  The g-step multi-variable optimization is the named residual (grid-verified, not
    symbolic).  conjecture1_proved = False."""

    census_jp: int = 30
    tail_check_to: int = 200

    def tail_is_nonneg_coeff_polya(self) -> bool:
        """The tail identity holds and every `P(k)` coefficient is `>= 0` (so `positivity`/`Nat.le_add_right`
        closes the Lean tail) -- and the constant term equals the tight base `621*6^11 - 64*7^11`."""
        if not all(c >= 0 for c in TAIL_P_COEFFS):
            return False
        if TAIL_P_COEFFS[-1] != 621 * 6 ** 11 - 64 * 7 ** 11:
            return False
        return all(tail_identity_holds(k) for k in range(0, 25))

    def per_step_tail_holds(self) -> bool:
        """`64*(m+1)^11 <= 621*m^11` for every integer `m` in `[6, tail_check_to]`, and FAILS at `m=4` (so the
        base `m>=6` is not slack padding -- `m=5` already holds, `m=4` does not)."""
        if any(not per_step_holds(m) for m in range(6, self.tail_check_to + 1)):
            return False
        return per_step_holds(5) and not per_step_holds(4)

    def base_equality_and_descent(self) -> bool:
        """`B(0,j') = (3/2)^11` exactly for every `j'`, and `B(L,j') <= (3/2)^11` for all `0 <= L <= j'`, with
        equality iff `L = 0` -- the full Inequality 1, validated over the census."""
        for jp in range(0, self.census_jp + 1):
            if B(0, jp) != THREE_HALVES_11:
                return False
            for L in range(0, jp + 1):
                if B(L, jp) > THREE_HALVES_11:
                    return False
                if L >= 1 and B(L, jp) >= THREE_HALVES_11:
                    return False
        return True

    def j2_final_certificate(self) -> bool:
        """The exact rational chain: `gamma = W^2(5/3)^11`, `W*gamma^2 = W^5(5/3)^22 < 486/529`, and the
        cross-multiplied integer certificate `64^3*50^11 < 621^3*27^11`."""
        if GAMMA != W ** 2 * Fr(5, 3) ** 11:
            return False
        if W * GAMMA ** 2 != W ** 5 * Fr(5, 3) ** 22:
            return False
        if not (W * GAMMA ** 2 < F_ARM):
            return False
        # the rational cert is exactly W*gamma^2 / (486/529)
        if W * GAMMA ** 2 / F_ARM != W ** 3 * Fr(50, 27) ** 11:
            return False
        return final_rational_certificate()

    def finding(self) -> str:
        return (
            "R1's two scalar inequalities pinned to kernel-checkable form + exact-arithmetic validated. "
            "INEQ 1 (B(L,j') <= (3/2)^11): base B(0,j')=(3/2)^11 (cancel j'+1) + descent via the INTEGER TAIL "
            "64(m+1)^11 <= 621 m^11 (m=3j'+L+2 >= 6), kernel-tight by the all-nonneg-coefficient Polya identity "
            "621(6+k)^11 = 64(7+k)^11 + P(k). INEQ 2 (j=2 closure): final rational certificate "
            "W*gamma^2 = W^5(5/3)^22 < 486/529, i.e. 64^3*50^11 < 621^3*27^11 (W^3(50/27)^11 < 1). Emitted to "
            "G1.ArmExtremality (import Mathlib; tail by Nat.le_add_right on the Polya identity, cert by norm_num). "
            "RESIDUAL: the g-lemma's inductive step is a multi-variable optimization (max < gamma; crude "
            "separable bound ~8.9 > gamma, so the two-regime product is load-bearing) -- grid-verified "
            "(reconstruction ~2.552 < gamma=2.928; write-up 2.538), NOT yet symbolic. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Validates both families in exact arithmetic -- the green gate for the emitted Lean theorems.  NOT
        the g-step optimization (named residual), NOT BG."""
        return (
            self.tail_is_nonneg_coeff_polya()
            and self.per_step_tail_holds()
            and self.base_equality_and_descent()
            and self.j2_final_certificate()
        )
