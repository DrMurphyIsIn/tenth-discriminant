"""The redirected resonance carrier -- where the Lehmer "=1-or-gap" actually lives (p = 23).

Two Tier-B probes converged on the same redirect:
  * #1 (`mahler.py`) sought a Lehmer `=1`-or-gap but found the ARCHIMEDEAN Mahler measure of the
    matching / D+iA polynomials is a spectral-radius growth with NO gap -- because BG's density has
    `sup D = 1` *approached*, not a Lehmer gap.
  * #2 (`ehrhart_bg.py`) sought `23 | denominator` but the tree matching polytope is INTEGRAL
    (bipartite), Ehrhart period 1 -- no 23.
Both point here: the gap is not archimedean and not in a matching polytope -- it is the **23-adic
absolute value of `Phi^11` itself**.

THE CARRIER.  With `Phi^11 = (64/621)^n (prod a_v)^11` (amplitude form, `sporadic_tie.amp_product`),
put `delta(T) = v_23(Phi^11) = 11 v_23(prod a_v) - n`  (an INTEGER), and
    |Phi^11|_23  =  23^(-delta)   in { ..., 23^2, 23, 1, 1/23, ... }.
This is a discrete set with a MULTIPLICATIVE GAP of 23 around 1 -- exactly the Lehmer `=1`-or-gap
SHAPE probe #1 wanted, and a genuine `23`-divisibility exactly as probe #2 wanted, married in ONE
object.  A tie needs `Phi^11 = 1`, hence `|Phi^11|_23 = 1`, hence `delta = 0`.

VERIFIED STRUCTURE (this module).
  1. Adelic PRODUCT FORMULA `prod_v |Phi^11|_v = 1` on all trees -- the identity that makes the
     archimedean size `|Phi^11|_inf = Phi^11 <= 1` and the 23-adic size `23^(-delta)` two faces of one
     rational.  (Phi^11 carries many primes -- dead-end #5 -- but 23 is the BINDING place: `v_23(621)=1`.)
  2. The tie `N(0,5)` sits at `|Phi^11|_23 = 1` (`delta = 0`); off-tie near-stars have `delta = -n`, so
     `|Phi^11|_23 = 23^n` -- the gap WIDENS.  The 23-adic place SEES the isolation the archimedean place
     only approaches.
  3. CATEGORICAL 23-adic strictness for `11 ∤ n`: every tree with `n` not a multiple of 11 has
     `delta != 0`, hence `Phi^11 != 1` -- an ARITHMETIC (not size, not integrality-floor) reason.  Given
     the `<=` half, `Phi^11 < 1` strictly, with no analytic estimate.

WHAT THIS DOES AND DOES NOT DO.  It IDENTIFIES the correct carrier (answering both probes' redirect),
supplies the product-formula identity, and gives categorical strictness on the `11 ∤ n` locus,
cleanly SEPARATING BG into:
    (a) `11 ∤ n`  -- closed 23-adically (given the `<=` half): `Phi^11 != 1` for free;
    (b) `11 ∣ n`  -- the irreducible core, where `delta = 0` can recur for NON-ties (the open
        sporadic-tie danger) and the archimedean density / collective-cancellation bound must re-enter.
It does NOT close (b), and the `<=` half is still open.  This is a reframing + verified identities +
a strictness lemma on half the domain, not a proof.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from ..padic import padic_val_frac

P_BIND = 23  # the binding prime: v_23(621) = 1, so 621 = 3^3 * 23


def phi11_23adic_valuation(n, edges) -> int:
    """`delta(T) = v_23(Phi^11)`, an integer.  Equals `11 v_23(prod a_v) - n` by the amplitude form.
    A tie forces `delta = 0` (Phi^11 = 1); `delta = 0` requires 11 | n (since delta = 11 v_23(..) - n)."""
    from .rooted_phi import bg_phi11_fast
    return padic_val_frac(bg_phi11_fast(n, edges), P_BIND)


def phi11_23adic_size(n, edges) -> Fr:
    """`|Phi^11|_23 = 23^(-delta)` -- the 23-adic size, an integer power of 23.  `1` iff `delta = 0`."""
    d = phi11_23adic_valuation(n, edges)
    return Fr(P_BIND) ** (-d)


def _prime_support(m: int):
    import sympy as sp
    return set(sp.factorint(abs(m)).keys()) if m else set()


def adelic_product(n, edges) -> Fr:
    """`prod_v |Phi^11|_v` over ALL places: `|Phi^11|_inf` times `p^(-v_p(Phi^11))` for every prime p
    dividing the numerator or denominator.  By the product formula this is exactly `1` for any rational."""
    from .rooted_phi import bg_phi11_fast
    q = bg_phi11_fast(n, edges)
    primes = _prime_support(q.numerator) | _prime_support(q.denominator)
    prod = Fr(abs(q.numerator), q.denominator)  # |q|_inf  (q >= 0 here)
    for p in primes:
        prod *= Fr(p) ** (-padic_val_frac(q, p))
    return prod


@dataclass(frozen=True)
class ResonanceCarrierCertificate:
    """The 23-adic carrier: `|Phi^11|_23 = 23^(-delta)` is the Lehmer `=1`-or-gap object both Tier-B
    probes redirected to.  Certifies (i) the adelic product formula on all trees <= n_max, (ii) the tie
    is a 23-adic unit, (iii) categorical strictness `Phi^11 != 1` on `11 ∤ n`, and (iv) the gap widens
    off the tie on the near-star family.  These are real identities/lemmas -- NOT a proof of BG.  See
    the module docstring for the honest scope (the `11 | n` core stays open)."""

    n_max: int = 9          # exhaustive over all trees to here (all have n not a multiple of 11 -> 23-gate)
    near_star_s: tuple = (2, 3, 4, 5, 6, 7, 8)
    tie_s: int = 5          # N(0,5) is the n = 11 tie

    def _edges(self, T):
        idx = {v: i for i, v in enumerate(T.nodes())}
        return T.number_of_nodes(), tuple((idx[a], idx[b]) for a, b in T.edges())

    def product_formula_holds(self) -> bool:
        """`prod_v |Phi^11|_v = 1` for every tree up to n_max (the adelic identity)."""
        import networkx as nx
        for n in range(2, self.n_max + 1):
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                if adelic_product(nn, e) != 1:
                    return False
        return True

    def tie_is_23adic_unit(self) -> bool:
        """The tie N(0,5): Phi^11 = 1, so delta = 0 and |Phi^11|_23 = 1 (the surviving place-1 condition)."""
        from .matching_free_energy import near_star_edges
        from .rooted_phi import bg_phi11_fast
        n, e = near_star_edges(self.tie_s)
        return (bg_phi11_fast(n, e) == 1
                and phi11_23adic_valuation(n, e) == 0
                and phi11_23adic_size(n, e) == 1)

    def categorical_strictness_off_11(self) -> bool:
        """For every tree with 11 ∤ n up to n_max: delta = v_23(Phi^11) != 0, hence Phi^11 != 1 --
        arithmetic strictness with no size argument.  (These n never tie; the 23-gate proves it directly.)"""
        import networkx as nx
        for n in range(2, self.n_max + 1):
            if n % 11 == 0:
                continue
            for T in nx.nonisomorphic_trees(n):
                nn, e = self._edges(T)
                if phi11_23adic_valuation(nn, e) == 0:   # would allow Phi^11 = 1 at 11 ∤ n
                    return False
        return True

    def gap_widens_off_tie(self) -> bool:
        """On the near-star family: the tie has |Phi^11|_23 = 1 while every off-tie N(0,s) has
        |Phi^11|_23 = 23^n > 1 (delta = -n = -(2s+1)); the 23-adic gap grows away from the tie."""
        from .matching_free_energy import near_star_edges
        for s in self.near_star_s:
            n, e = near_star_edges(s)
            size = phi11_23adic_size(n, e)
            if s == self.tie_s:
                if size != 1:
                    return False
            else:
                if not size > 1:                       # off-tie: strictly gapped away from 1
                    return False
        return True

    def carrier_table(self):
        """(s, n, delta, |Phi^11|_23) over the near-star family -- the gap picture."""
        from .matching_free_energy import near_star_edges
        out = []
        for s in self.near_star_s:
            n, e = near_star_edges(s)
            out.append((s, n, phi11_23adic_valuation(n, e), phi11_23adic_size(n, e)))
        return out

    def finding(self) -> str:
        return (
            "REFRAME + PARTIAL. The carrier both Tier-B probes redirected to is the 23-adic absolute "
            "value |Phi^11|_23 = 23^(-delta): a discrete set with a multiplicative gap of 23 around 1 "
            "(the Lehmer =1-or-gap SHAPE probe #1 lacked archimedean-ly, and the 23-divisibility probe #2 "
            "lacked in the integral matching polytope). Verified: the adelic product formula ties |.|_inf "
            "to |.|_23; the tie is the unique surviving |.|_23 = 1 requirement; the gap WIDENS off the tie "
            "(delta = -n on near-stars). This gives CATEGORICAL strictness Phi^11 != 1 on 11 ∤ n (no size "
            "argument), separating BG into (a) 11 ∤ n -- closed 23-adically given the <= half, and (b) "
            "11 | n -- the irreducible core where delta = 0 can recur for non-ties (open sporadic-tie "
            "danger) and the archimedean density bound must re-enter. Does NOT close (b) or the <= half. "
            "conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the verified identities/lemmas (product formula, tie = 23-adic unit, categorical
        strictness on 11 ∤ n, gap-widening) -- NOT BG."""
        return (
            self.product_formula_holds()
            and self.tie_is_23adic_unit()
            and self.categorical_strictness_off_11()
            and self.gap_widens_off_tie()
        )

    def lean(self) -> str:
        return (
            "-- RESONANCE CARRIER (23-adic): |Phi^11|_23 = 23^(-v_23(Phi^11)) is the =1-or-gap object.\n"
            "-- Product formula for q : Rat gives |q|_inf * prod_p p^(-v_p q) = 1 (Rat adelic valuation).\n"
            "-- Categorical strictness on (11 does not divide n): v_23(Phi^11) = 11 v_23(prod a_v) - n;\n"
            "-- if 11 does not divide n then v_23(Phi^11) != 0, so Phi^11 != 1.  (v_23(621)=1 core below.)\n"
            "theorem v23_621_unit : (¬ (23^2 ∣ (621:ℤ))) ∧ (23 ∣ (621:ℤ)) := by norm_num\n"
        )
