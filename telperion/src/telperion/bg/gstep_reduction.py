"""The g-step multi-variable optimization, reduced toward Lean-tight (the last residual of single-hub R1).

R1's single-hub arm-extremality rests on the g-lemma `g(C) <= gamma := W^2 (5/3)^11` for every non-leaf block
`C`.  Its strong-induction step, in the all-non-leaf (branching, root-degree `j' >= 2`) case, is a genuine
MULTI-VARIABLE optimization over the child messages `mu_1, ..., mu_{j'} in (0, 1/2]`:

    g_bound(mu_1..mu_{j'}) = W * [1 + (3*sum mu_i + 1)/(3j'+3)]^11 * prod_i min(1, gamma/(1+mu_i/3)^11)  <  gamma.

A crude separable bound blows past gamma (~8.9), so the two-regime product `min(1, gamma/(1+mu_i/3)^11)` is
load-bearing (collective cancellation).  This module records the REDUCTION of that optimization to a finite
rational certificate, validated in exact/tight arithmetic.

REDUCTION -- COORDINATE-WISE UNIMODALITY (NOT majorization).  A key correction: `g_bound` is Schur-CONVEX
for fixed sum (in the heavy regime `ln(min(1,gamma/(1+mu/3)^11))` is convex), so the "Schur-concavity =>
symmetric argmax" route DOES NOT apply.  The global max is nonetheless at the symmetric crossover `mu*`
(`(1+mu*/3)^11 = gamma`), by a coordinate-wise argument -- verified here by multi-start search (the true
box-max equals the symmetric-`mu*` value to machine precision for `j' = 2..6`):

  (T1) on `{all mu_i <= mu*}`: each factor is `1`, so `g_bound = W*boost^11` is INCREASING in every
       coordinate (boost up) -- push each `mu_i` UP to `mu*`.
  (T2) on `{all mu_i >= mu*}`: the descent condition `(j'+1)*boost > 3+mu_i` holds throughout (RATIONAL
       ENGINE: `(j'+1)*boost >= (j'+1) + (3S+1)/3 >= j' + 4/3 + mu_i >= 3+mu_i` for `j' >= 2`, since
       `j'+4/3 >= 3`), so `d/dmu_i log g_bound < 0` -- decreasing any coordinate DOWN to `mu*` raises
       `g_bound`.
  => global max = `g_bound(mu*,...,mu*) = W*boost(mu*)^11`.  (The pivot is the IRRATIONAL `mu*`; capping at
  the rational `1/3` instead does NOT work -- it overshoots the per-coordinate optimum and can decrease
  `g_bound`.)

Then `boost(mu*) < 4/3` (from `3*mu* < 1`), so `f_{j'>=2}(mu*) = W*boost(mu*)^11 < W*(4/3)^11 < gamma`.  Two
EXACT rational leaves close it:
    (I)  mu* < 1/3        <=>  gamma < (10/9)^11   <=>  64^2*5^11*9^11 < 621^2*3^11*10^11,
    (II) W*(4/3)^11 < gamma                        <=>  621*4^11 < 64*5^11.
(`j' = 1` is chain-absorbed by the `B(L,j')` family; only `j' >= 2` branching goes through this optimization.)

STATUS.  T1/T2 are the coordinate-wise unimodality glue, verified numerically here; the descent engine (T2)
and both leaves are exact rationals.  Emitted to Lean (`G1.ArmExtremality`): the two leaves plus the descent
engine `descent_engine` and `boost_le_four_thirds`.  Remaining for full Lean-lock of the g-lemma: the
over-the-reals T1/T2 unimodality at the irrational `mu*`, and wiring both families into the block-level
g-lemma (the Branch induction).  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

W = Fr(64, 621)
GAMMA = W ** 2 * Fr(5, 3) ** 11
_GF = float(GAMMA)
MU_STAR = 3.0 * (_GF ** (1.0 / 11.0) - 1.0)          # crossover: (1+mu*/3)^11 = gamma


def _m(mu: float) -> float:
    """The two-regime per-child factor `min(1, gamma/(1+mu/3)^11)`."""
    return min(1.0, _GF / (1.0 + mu / 3.0) ** 11)


def g_bound(mus) -> float:
    """`W * [1+(3*sum+1)/(3j'+3)]^11 * prod min(1, gamma/(1+mu_i/3)^11)`  (the relaxed g-step upper bound)."""
    jp = len(mus)
    S = sum(mus)
    boost = (1.0 + (3.0 * S + 1.0) / (3.0 * jp + 3.0)) ** 11
    prod = 1.0
    for mu in mus:
        prod *= _m(mu)
    return float(W) * boost * prod


def f_sym(jp: int, mu: float) -> float:
    """The symmetric single-variable reduction `f_{j'}(mu)`."""
    return g_bound([mu] * jp)


def leaf_mu_star_lt_third() -> bool:
    """(I) `mu* < 1/3`, as the exact rational `gamma < (10/9)^11`  (`64^2*5^11*9^11 < 621^2*3^11*10^11`)."""
    return GAMMA < Fr(10, 9) ** 11


def leaf_W_four_thirds_lt_gamma() -> bool:
    """(II) `W*(4/3)^11 < gamma`, as the exact rational `621*4^11 < 64*5^11`."""
    return W * Fr(4, 3) ** 11 < GAMMA


def descent_engine_holds(jp: int, S: Fr, mu: Fr) -> bool:
    """The RATIONAL T2 engine: for `jp >= 2` and `mu <= S`, `(jp+1)*boost(jp,S) >= 3 + mu`
    (via `(jp+1)*boost = (jp+1) + (3S+1)/3 >= jp + 4/3 + mu >= 3 + mu`)."""
    boost = 1 + Fr(3 * S + 1, 3 * jp + 3)
    return (jp + 1) * boost >= 3 + mu


def boost_le_four_thirds_when_small(jp: int, S: Fr) -> bool:
    """`3*S <= jp` (all `mu_i <= 1/3`) implies `boost(jp,S) <= 4/3`."""
    return 1 + Fr(3 * S + 1, 3 * jp + 3) <= Fr(4, 3)


@dataclass(frozen=True)
class GStepReductionCertificate:
    """The branching (j' >= 2) g-step optimization, reduced by COORDINATE-WISE UNIMODALITY (not majorization:
    `g_bound` is Schur-CONVEX for fixed sum).  `check()` validates: the box-max is at the symmetric crossover
    `mu*` (multi-start, machine precision); T1 (increasing below `mu*`); the T2 rational descent engine
    `(j'+1)*boost >= 3+mu` for `j' >= 2`; `boost(mu*) < 4/3`; and the two exact rational leaves.  The
    over-the-reals T1/T2 unimodality at the irrational `mu*` + the Branch-induction wiring are the residual;
    the descent engine, the boost bound, and both leaves are exact and Lean-emitted.  NOT the full g-lemma,
    NOT BG.  conjecture1_proved = False."""

    max_jp: int = 40

    def box_max_is_symmetric_mustar(self) -> bool:
        """Multi-start + targeted boundary probes: no asymmetric config beats `g_bound(mu*,...,mu*)` (the
        Schur-convex function's global max is nonetheless the symmetric crossover)."""
        import random
        rng = random.Random(7)
        for jp in range(2, 7):
            ref = g_bound([MU_STAR] * jp)
            for _ in range(4000):
                x = [rng.uniform(1e-4, 0.5) for _ in range(jp)]
                for _it in range(40):
                    i = rng.randrange(jp)
                    xn = x[:]
                    xn[i] = min(0.5, max(1e-5, xn[i] + rng.uniform(-0.05, 0.05)))
                    if g_bound(xn) > g_bound(x):
                        x = xn
                if g_bound(x) > ref + 1e-9:
                    return False
            for k in range(0, jp + 1):                       # boundary probes: k heavy + rest tiny / at mu*
                if g_bound([0.5] * k + [1e-4] * (jp - k)) > ref + 1e-9:
                    return False
                if g_bound([0.5] * k + [MU_STAR] * (jp - k)) > ref + 1e-9:
                    return False
        return True

    def t1_increasing_below_mustar(self) -> bool:
        """On `{all mu_i <= mu*}` (every factor = 1), `g_bound = W*boost^11` is increasing in each coordinate."""
        import random
        rng = random.Random(1)
        for jp in range(2, 7):
            for _ in range(3000):
                mus = [rng.uniform(1e-4, MU_STAR) for _ in range(jp)]
                i = rng.randrange(jp)
                hi = mus[:]
                hi[i] = min(MU_STAR, mus[i] + 1e-4)
                if g_bound(hi) < g_bound(mus) - 1e-12:
                    return False
        return True

    def t2_descent_engine(self) -> bool:
        """The RATIONAL descent engine `(j'+1)*boost >= 3+mu` for `j' >= 2`, `mu <= S` (exact), and its
        numeric consequence: `(j'+1)*boost > 3+mu_i` throughout `{all mu_i >= mu*}`."""
        for jp in range(2, self.max_jp + 1):                 # exact rational engine
            for sn in range(0, jp * 50 + 1, 7):
                S = Fr(sn, 100)
                for mn in range(0, min(sn, 50) + 1, 5):
                    if not descent_engine_holds(jp, S, Fr(mn, 100)):
                        return False
        import random
        rng = random.Random(2)
        for jp in range(2, 9):                                # numeric consequence on {mu_i >= mu*}
            for _ in range(3000):
                mus = [rng.uniform(MU_STAR, 0.5) for _ in range(jp)]
                boost = 1.0 + (3.0 * sum(mus) + 1.0) / (3.0 * jp + 3.0)
                if not all((jp + 1) * boost > 3.0 + mu for mu in mus):
                    return False
        return True

    def boost_star_below_four_thirds(self) -> bool:
        """`boost(mu*) < 4/3` for every `j' >= 2` (from `3*mu* < 1`), and the rational form `3*S <= j' =>
        boost <= 4/3`."""
        if not MU_STAR < 1.0 / 3.0:
            return False
        for jp in range(2, self.max_jp + 1):
            boost = 1.0 + (3.0 * jp * MU_STAR + 1.0) / (3.0 * jp + 3.0)
            if not boost < 4.0 / 3.0:
                return False
            if not boost_le_four_thirds_when_small(jp, Fr(jp, 3)):   # 3S = jp is the tight case (=4/3)
                return False
        return True

    def rational_leaves(self) -> bool:
        """The two exact rational leaves, chaining to `f_{j'>=2}(mu*) < gamma`."""
        if not (leaf_mu_star_lt_third() and leaf_W_four_thirds_lt_gamma()):
            return False
        if not (64 ** 2 * 5 ** 11 * 9 ** 11 < 621 ** 2 * 3 ** 11 * 10 ** 11):
            return False
        if not (621 * 4 ** 11 < 64 * 5 ** 11):
            return False
        return float(W * Fr(4, 3) ** 11) < _GF and f_sym(2, MU_STAR) < float(W * Fr(4, 3) ** 11)

    def finding(self) -> str:
        return (
            "The branching (j'>=2) g-step max < gamma, reduced by COORDINATE-WISE UNIMODALITY (NOT majorization "
            "-- g_bound is Schur-CONVEX for fixed sum, so the Schur route fails). Global box-max = symmetric "
            "crossover mu* (multi-start verified). T1: increasing below mu* (factors=1, boost up). T2 rational "
            "engine: (j'+1)*boost = (j'+1)+(3S+1)/3 >= j'+4/3+mu >= 3+mu for j'>=2, so g_bound decreases toward "
            "mu* above it. => max = W*boost(mu*)^11; boost(mu*)<4/3 (3 mu*<1), so < W(4/3)^11 < gamma. Two EXACT "
            "rational leaves: (I) mu*<1/3 <=> gamma<(10/9)^11 <=> 64^2*5^11*9^11 < 621^2*3^11*10^11; (II) "
            "W(4/3)^11<gamma <=> 621*4^11 < 64*5^11. NOTE: the pivot is the IRRATIONAL mu*; capping at rational "
            "1/3 does NOT work (overshoots, can decrease g_bound). Lean-emitted (G1.ArmExtremality): the two "
            "leaves + descent_engine + boost_le_four_thirds. Residual: over-the-reals T1/T2 at mu* + Branch "
            "wiring. (j'=1 chain-absorbed by B(L,j').) conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Validates the coordinate-wise unimodality reduction (box-max symmetric, T1, the T2 rational descent
        engine, boost(mu*)<4/3) and the two exact rational leaves.  The over-the-reals unimodality + Branch
        wiring are the named residual.  NOT the full g-lemma."""
        return (
            self.box_max_is_symmetric_mustar()
            and self.t1_increasing_below_mustar()
            and self.t2_descent_engine()
            and self.boost_star_below_four_thirds()
            and self.rational_leaves()
        )
