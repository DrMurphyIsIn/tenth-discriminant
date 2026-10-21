"""Quantitative 23-gate-strictness: an arithmetic lower bound on the Brualdi-Goldwasser deficit.

PROOF_STATUS's live lead: prove the deficit `1 - Phi^11 > 0` for non-tie trees is bounded below by an
ARITHMETIC (not smooth, not local) quantity -- the 23-gate as the anchor, strictness as the frontier.  This
module makes the strictness quantitative, refining `sporadic_tie`'s crude integrality floor `1/D`.

THE DIOPHANTINE FRAME.  With `rho_B = (621/64)^(1/11)` (root of `64 x^11 - 621`, `621 = 3^3 * 23`),

    BG (rooted)   <=>   prod_v a_v  <=  rho_B^n .

For `11 | n`, `rho_B^n = (621/64)^(n/11)` is RATIONAL and equality (a tie) is possible.  For `11 \nmid n`,
`rho_B^n` is a degree-11 ALGEBRAIC IRRATIONAL (root of `64^n x^11 - 621^n`), while `prod a_v` is RATIONAL --
so `prod a_v != rho_B^n` categorically, hence `Phi^11 != 1`, hence (given the open `<=` half) `Phi^11 < 1`.
The tie N(0,5) is the unique equality point; `(621/64)^(n/11)` is rational exactly when `11 | n` (no exponent
in `621/64 = 2^-6 3^3 23` is a multiple of 11).

THE EXACT DEFICIT INTEGER.  Write `prod a_v = P/Q`.  Then `Phi^11 = 64^n P^11 / (621^n Q^11)` and

    1 - Phi^11  =  M / D ,    M = 621^n Q^11 - 64^n P^11 (a nonneg integer),   D = 621^n Q^11 .

Non-tie => `M >= 1` (integrality): `1 - Phi^11 >= 1/D` (the crude floor).

THE 23-ADIC REFINEMENT (the quantitative gate).  `M` is divisible by `23^{v_23(M)}`, so

    1 - Phi^11  >=  23^{v_23(M)} / D ,

a strictly stronger, purely arithmetic bound.  And `v_23(M)` is LARGE exactly on the near-1 family where
strictness is hardest: on the tie-recursive family `hub + k*N(0,5)` it is `v_23(M) = 11(k-1)` (verified),
growing linearly -- the two terms `621^n Q^11` and `64^n P^11` are 23-adically close there.  So the 23-gate
supplies its strongest deficit bound on precisely the structures that approach `Phi^11 = 1`.

HONEST SCOPE.  This quantifies the STRICTNESS (turns `<=` into a `<` with an explicit arithmetic bound,
refining `1/D` by the factor `23^{v_23(M)}`) and pins the Diophantine/algebraic anchor (`rho_B^n` degree 11,
`621 = 3^3 * 23`).  It does NOT prove the `<=` half (`Phi^11 <= 1`), the open collective-cancellation crux.
The bound is arithmetic and real but not tight (the true tie-recursive deficit is Theta(1)).
`conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from ..padic import padic_val_frac
from .sporadic_tie import amp_product


def deficit_integer(n, edges, root: int = 0):
    """`(M, D)` with `1 - Phi^11 = M/D`, `M = 621^n Q^11 - 64^n P^11` (nonneg integer for `Phi^11 <= 1`),
    `D = 621^n Q^11`, where `prod a_v = P/Q`.  `M = 0` iff the tree is a tie at this root."""
    pa = amp_product(n, edges, root)
    P, Q = pa.numerator, pa.denominator
    D = 621 ** n * Q ** 11
    M = D - 64 ** n * P ** 11
    return M, D


def deficit_23_valuation(n, edges, root: int = 0):
    """`v_23(M)` -- the 23-adic valuation of the exact deficit integer (`None` at a tie, where `M = 0`)."""
    M, _ = deficit_integer(n, edges, root)
    return None if M == 0 else padic_val_frac(Fr(M), 23)


def strictness_bound(n, edges, root: int = 0) -> Fr:
    """The 23-gate strictness bound on the deficit: `23^{v_23(M)} / D <= 1 - Phi^11` (refines `1/D`)."""
    M, D = deficit_integer(n, edges, root)
    if M == 0:
        return Fr(0)
    return Fr(23) ** padic_val_frac(Fr(M), 23) / D


def rho_b_power_is_rational(n: int) -> bool:
    """Is `rho_B^n = (621/64)^(n/11)` rational?  True iff `11 | n` -- the only case allowing a tie (equality)."""
    return n % 11 == 0


@dataclass(frozen=True)
class GateStrictnessCertificate:
    """Quantitative 23-gate-strictness: the deficit `1 - Phi^11` for non-tie trees is bounded below by the
    arithmetic quantity `23^{v_23(M)}/D`, refining the crude `1/D` floor; `rho_B^n` is a degree-11 algebraic
    irrational for `11 \\nmid n` (Diophantine anchor).  `check()` certifies these arithmetic facts -- NOT the
    open `<=` half, and NOT BG.  See the module docstring for scope.  conjecture1_proved = False."""

    near_star_s: tuple = (2, 3, 4, 6, 7, 8)     # 11 does not divide n = 2s+1 here (tie s=5 excluded)
    tie_recursive_k: tuple = (1, 2, 3, 4, 5)

    def equality_needs_11_divides_n(self) -> bool:
        """`(621/64)^(n/11)` is rational (tie/equality possible) iff `11 | n` -- verified over a range."""
        for n in range(2, 40):
            r = rho_b_power_is_rational(n)
            # 11 | n <=> the rational (621/64)^n is a perfect 11th power of a rational
            from sympy import Rational, nsimplify
            actually = bool(nsimplify(Rational(621, 64) ** Rational(n, 11)).is_rational)
            if r != actually:
                return False
        return True

    def tie_is_the_unique_equality(self) -> bool:
        """The tie N(0,5) has `M = 0` (equality); every off-tie near-star has `M >= 1`."""
        from .frustration_free import near_star_edges
        n5, e5 = near_star_edges(5)
        if deficit_integer(n5, e5, 0)[0] != 0:
            return False
        for s in self.near_star_s:
            n, e = near_star_edges(s)
            if deficit_integer(n, e, 0)[0] < 1:
                return False
        return True

    def deficit_23_refinement_grows_on_tie_recursive(self) -> bool:
        """On the tie-recursive family `hub + k*N(0,5)` the deficit integer has `v_23(M) = 11(k-1)`,
        growing linearly -- the 23-gate strictness bound `23^{11(k-1)}/D` bites on the near-1 family."""
        from .frustration_free import tie_recursive_edges
        for k in self.tie_recursive_k:
            n, e = tie_recursive_edges(k)
            if deficit_23_valuation(n, e, 0) != 11 * (k - 1):
                return False
        return True

    def strictness_bounds_are_valid(self) -> bool:
        """The arithmetic bound `23^{v_23(M)}/D <= 1 - Phi^11` holds (and refines `1/D`) for every non-tie
        tree tested (near-stars and tie-recursive)."""
        from .frustration_free import near_star_edges, tie_recursive_edges
        from .rooted_phi import bg_phi11_fast
        cases = [near_star_edges(s) for s in self.near_star_s] + \
                [tie_recursive_edges(k) for k in self.tie_recursive_k]
        for n, e in cases:
            M, D = deficit_integer(n, e, 0)
            deficit = Fr(1) - bg_phi11_fast(n, e)
            if M == 0:
                continue
            bound = strictness_bound(n, e, 0)
            if not (Fr(1, D) <= bound <= deficit):     # 1/D <= 23^v/D <= actual deficit
                return False
        return True

    def finding(self) -> str:
        return (
            "QUANTITATIVE STRICTNESS (arithmetic), not a proof of the <= half. BG <=> prod a_v <= rho_B^n; "
            "for 11 does-not-divide n, rho_B^n = (621/64)^(n/11) is a degree-11 ALGEBRAIC IRRATIONAL (root of "
            "64^n x^11 - 621^n, 621 = 3^3*23) while prod a_v is rational, so Phi^11 != 1 categorically; the tie "
            "N(0,5) is the unique equality point (rational rho_B^n needs 11|n). The exact deficit integer "
            "M = 621^n Q^11 - 64^n P^11 gives 1-Phi^11 = M/D >= 1/D (integrality), REFINED to "
            "1-Phi^11 >= 23^{v_23(M)}/D by the 23-adic valuation of M. And v_23(M) is large exactly where "
            "strictness is hardest: on the tie-recursive family it equals 11(k-1), growing linearly, so the "
            "23-gate supplies its strongest deficit bound on the near-1 structures. This quantifies the "
            "strictness with an explicit arithmetic factor 23^{v_23(M)}; it does NOT prove the open <= half. "
            "conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the Diophantine anchor (equality needs 11|n), the tie as the unique equality point, the
        linear-growth 23-adic refinement on the tie-recursive family, and the validity of the arithmetic
        strictness bound -- NOT the <= half, NOT BG."""
        return (
            self.equality_needs_11_divides_n()
            and self.tie_is_the_unique_equality()
            and self.deficit_23_refinement_grows_on_tie_recursive()
            and self.strictness_bounds_are_valid()
        )

    def lean(self) -> str:
        return (
            "-- 23-GATE STRICTNESS: BG <=> prod a_v <= rho_B^n, rho_B = (621/64)^(1/11).  For 11 \\nmid n,\n"
            "-- rho_B^n is a degree-11 algebraic irrational (root of 64^n x^11 - 621^n, 621 = 3^3*23), so\n"
            "-- prod a_v (rational) != rho_B^n; deficit M = 621^n Q^11 - 64^n P^11 >= 23^{v_23 M} (>= 1).\n"
            "theorem v23_621 : (¬ (23^2 ∣ (621:ℤ))) ∧ (23 ∣ (621:ℤ)) := by norm_num\n"
            "theorem rhoB_min_poly : (64:ℤ) * ? = 621 -- x^11 = 621/64; 64 x^11 - 621 = 0 is the anchor\n"
        )
