"""Residual of the single-hub `<=` half: a first-order-condition bound closes the interior-max non-arm blocks.

After `interior_max.py`, single-hub BG is reduced to: for interior-max (`k* >= 2`) NON-arm large-message
blocks, prove `Phi^11_hub(k*) <= 1`.  This module supplies the tool -- a first-order-condition (FOC) upper
bound that eliminates `F_B` -- and closes the residual on the census, reducing the remaining gap to one sharp
statement about the arm's uniqueness.

THE FOC BOUND (provable).  At the unique maximum `k*`, log-concavity gives `Phi^11_hub(k*+1) <= Phi^11_hub(k*)`,
i.e. `[a_hub(k*+1)/a_hub(k*)]^11 F_B <= 1`, i.e. `F_B <= [a_hub(k*)/a_hub(k*+1)]^11`.  Substituting into
`Phi^11_hub(k*) = (64/621) a_hub(k*)^11 F_B^{k*}` ELIMINATES `F_B`:

    Phi^11_hub(k*)  <=  B_up(k*, mu_B) := (64/621) * a_hub(k*)^{11(k*+1)} / a_hub(k*+1)^{11 k*} ,

a bound depending only on `(k*, mu_B)`, with `a_hub(k) = 1 + mu_B * k/(k+1)`.

THE FOC BOUND CLOSES THE RESIDUAL.  For every interior-max non-arm large-message block up to `n_B = 10`,
`B_up(k*, mu_B) <= 1` (max value `~0.426`), so `Phi^11_hub(k*) <= B_up <= 1` -- the residual is bounded, with
room to spare.  The FOC threshold: for fixed `mu`, `B_up(mu, k)` increases in `k` and crosses 1 at some
`K_max(mu)` (`K_max(1/3) = 4`, `K_max(3/11) = 10`, `K_max(1/4) = 22` -- smaller message, larger threshold);
the bound closes a block iff `k* <= K_max(mu_B)`.

THE ARM IS THE UNIQUE EXCEPTION.  The arm (`mu = 1/3`, the near-star) has `k* = 5 > K_max(1/3) = 4`, so
`B_up(1/3, 5) = 1.087 > 1` -- the FOC bound does NOT close the arm.  But the arm is exactly the block
`near_star_tail.py` proves directly (`Phi^11(N(0,s)) <= 1`, eq iff `s = 5`).  So single-hub BG closes as:
FOC bound for `k* <= K_max(mu)` (all non-arm blocks in the census) + `near_star_tail` for the arm.

THE REMAINING GAP (razor-thin, and sharp).  A fully uniform proof needs: NO non-arm block has
`k* > K_max(mu_B)`.  Since larger `k*` means slower decay (larger `F_B`), this is exactly "the arm uniquely
maximizes `F_B` (decay closest to 1) among large-message blocks, by enough of a margin that every other
block's `k*` stays under its FOC threshold."  Verified on the census (the arm's `F = 486/529 ~ 0.919` is the
isolated maximum; the next interior-max block has `F ~ 0.79`).  This is the single clean inequality left.
`conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .mixed_block_martingale import block_amplitude_and_message, block_factor

W = Fr(64, 621)
RHO_B_11 = Fr(621, 64)


def _a(mu: Fr, k: int) -> Fr:
    return 1 + mu * Fr(k, k + 1)


def family_phi_closed(mu: Fr, F: Fr, k: int) -> Fr:
    """`Phi^11_hub(k) = (64/621) a_hub(k)^11 F_B^k` (closed form)."""
    return W * _a(mu, k) ** 11 * F ** k


def foc_upper_bound(mu: Fr, kstar: int) -> Fr:
    """The FOC upper bound `B_up(k*, mu) = (64/621) a(k*)^{11(k*+1)} / a(k*+1)^{11 k*}` on `Phi^11_hub(k*)`
    at an interior maximum (eliminates `F_B` via `Phi^11_hub(k*+1) <= Phi^11_hub(k*)`)."""
    return W * _a(mu, kstar) ** (11 * (kstar + 1)) / _a(mu, kstar + 1) ** (11 * kstar)


def family_argmax(mu: Fr, F: Fr, K: int = 300) -> int:
    """The unique argmax `k*` of the log-concave family `Phi^11_hub(k)`."""
    best, ks = Fr(0), 0
    for k in range(1, K + 1):
        v = family_phi_closed(mu, F, k)
        if v > best:
            best, ks = v, k
        elif k > ks + 2:
            break
    return ks


def foc_threshold(mu: Fr, kmax: int = 200) -> int:
    """`K_max(mu)` = the largest `k` with `B_up(mu, k) <= 1` (the FOC bound closes a block iff `k* <= K_max`)."""
    last = 1
    for k in range(2, kmax + 1):
        if foc_upper_bound(mu, k) <= 1:
            last = k
        else:
            break
    return last


@dataclass(frozen=True)
class ResidualFOCCertificate:
    """Closes the interior-max non-arm residual of single-hub BG via the FOC bound, and pins the remaining
    gap to the arm's uniqueness.  `check()` certifies the FOC bound's validity and that it closes every
    interior-max non-arm block in the census, with the arm the unique exception (proven by near_star_tail) --
    NOT a fully uniform proof, NOT all of BG.  conjecture1_proved = False."""

    census_m: int = 9

    def _interior_non_arm_blocks(self):
        import networkx as nx
        for m in range(1, self.census_m + 1):
            trees = [nx.empty_graph(1)] if m == 1 else list(nx.nonisomorphic_trees(m))
            for T in trees:
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                for r in range(m):
                    alpha, mu = block_amplitude_and_message(m, e, r)
                    F = block_factor(m, e, r)
                    if (1 + mu) ** 11 <= RHO_B_11 or F > 1:
                        continue
                    ks = family_argmax(mu, F)
                    if ks >= 2 and not (mu == Fr(1, 3) and m == 2):
                        yield mu, F, ks

    def foc_bound_is_valid(self) -> bool:
        """`Phi^11_hub(k*) <= B_up(k*, mu)` for every interior-max non-arm block (the FOC inequality)."""
        for mu, F, ks in self._interior_non_arm_blocks():
            if not (family_phi_closed(mu, F, ks) <= foc_upper_bound(mu, ks)):
                return False
        return True

    def foc_closes_the_residual(self) -> bool:
        """`B_up(k*, mu) <= 1` for every interior-max non-arm block -> `Phi^11_hub(k*) <= 1` (residual closed
        on the census)."""
        return all(foc_upper_bound(mu, ks) <= 1 for mu, _F, ks in self._interior_non_arm_blocks())

    def arm_is_the_unique_foc_exception(self) -> bool:
        """The arm (`mu = 1/3`) has `k* = 5 > K_max(1/3) = 4`, so `B_up(1/3, 5) > 1` (FOC does not close it),
        while `B_up(1/3, k) <= 1` for `k <= 4`.  The arm is proven by `near_star_tail` (integer inequality)."""
        mu = Fr(1, 3)
        return (foc_threshold(mu) == 4
                and foc_upper_bound(mu, 5) > 1
                and 162 ** 11 * 486 < 161 ** 11 * 529     # near_star_tail's core, proves the arm family
                and family_phi_closed(mu, Fr(486, 529), 5) == 1)

    def residual_gap_is_kstar_below_threshold(self) -> bool:
        """The single remaining claim: every interior-max non-arm block has `k* <= K_max(mu)` (so the FOC
        bound closes it).  Equivalent to the arm uniquely maximizing `F_B` among large-message blocks -- its
        `F = 486/529` is the isolated maximum, verified on the census."""
        for mu, _F, ks in self._interior_non_arm_blocks():
            if ks > foc_threshold(mu):
                return False
        return True

    def finding(self) -> str:
        blocks = list(self._interior_non_arm_blocks())
        maxB = max((foc_upper_bound(mu, ks) for mu, _F, ks in blocks), default=Fr(0))
        return (
            "RESIDUAL CLOSED on the census via a first-order-condition bound; remaining gap is one sharp "
            "inequality. At the log-concave maximum k*, Phi^11_hub(k*+1) <= Phi^11_hub(k*) gives "
            "F_B <= [a(k*)/a(k*+1)]^11, which eliminates F_B: Phi^11_hub(k*) <= B_up(k*,mu) = "
            "(64/621) a(k*)^{11(k*+1)}/a(k*+1)^{11 k*}, a bound in (k*,mu) alone. For EVERY interior-max "
            f"non-arm block up to n_B={self.census_m}, B_up(k*,mu) <= {float(maxB):.3f} <= 1, so "
            "Phi^11_hub(k*) <= 1. The arm (mu=1/3) is the unique exception: k*=5 > K_max(1/3)=4, B_up>1, but "
            "near_star_tail proves it directly (162^11*486 < 161^11*529). So single-hub BG = FOC bound "
            "(k* <= K_max(mu)) + near_star_tail (the arm). Remaining uniform gap: no non-arm block has "
            "k* > K_max(mu) -- i.e. the arm (F=486/529) uniquely maximizes decay-nearest-to-1 among "
            "large-message blocks. A single clean inequality. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the FOC bound's validity, that it closes every interior-max non-arm block in the census,
        and the arm as the unique exception (proven by near_star_tail) -- NOT a uniform proof, NOT BG."""
        return (
            self.foc_bound_is_valid()
            and self.foc_closes_the_residual()
            and self.arm_is_the_unique_foc_exception()
            and self.residual_gap_is_kstar_below_threshold()
        )
