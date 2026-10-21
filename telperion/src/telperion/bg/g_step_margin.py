"""g-step margin study — is the config-based `Case2Property` closeable by a
continuous (Handelman/Putinar) certificate, or does it hit the integrality wall?

This ports the *exact* Lean quantities of `R3Cert.CappedJointConfig` (the corrected,
config-based open hypothesis of the capped-joint g-step, 2026-08-20) into exact
`Fraction` and answers ONE question for the BG closure programme:

    Is the case-2 g-step margin  1 - baseOf(l)^11 * prodBcap(l) / (W(5/3)^11)
    bounded away from 0, or does it collapse?

If the continuous margin is > 0 with room, the new Telperion Positivstellensatz
emitters (`emit_handelman`, `emit_constrained_sos`) can close Case 2.  If the
*continuous* statement is violated (margin < 0) at some message the recursion
cannot realize, then Case2Property is FALSE-as-stated over unrestricted `μ` and
the honest target needs the achievability (integrality) constraint on `μ` — the
same §4 obstruction relocated into the g-step, and a job for the *lattice*
emitters (`emit_padic`, `emit_cg_round`), not the continuous ones.

Exact `Fraction` at every decision point.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

# --- exact Lean-port constants (R3Cert.GStepCore / CappedJointConfig) ---------
W = Fr(64, 621)
GAMMA = W ** 2 * Fr(5, 3) ** 11          # γ = W²(5/3)¹¹ — the g-lemma constant
DENOM = W * Fr(5, 3) ** 11               # the Case2 denominator  (base^11 > DENOM ⇔ case 2)


def glemma(mu: Fr) -> Fr:
    """glemma(μ) = γ/(1+μ/3)¹¹  (R3Cert.CappedJointConfig.glemma)."""
    return GAMMA / (1 + mu / 3) ** 11


def master_ub(mu: Fr) -> Fr:
    """master_ub(μ) = W(3/(2+μ))¹¹  (…CappedJointConfig.master_ub)."""
    return W * (Fr(3) / (2 + mu)) ** 11


def Bcap(mu: Fr) -> Fr:
    """Bcap(μ) = min(master_ub, glemma, 1) — the per-child cap (…CappedJointConfig.Bcap)."""
    return min(master_ub(mu), min(glemma(mu), Fr(1)))


def baseOf(l) -> Fr:
    """baseOf l = (3d+3S+1)/(3d), d = |l|+1, S = Σl  (…CappedJointConfig.baseOf)."""
    d = len(l) + 1
    S = sum(l, Fr(0))
    return (3 * d + 3 * S + 1) / (3 * d)


def prodBcap(l) -> Fr:
    p = Fr(1)
    for mu in l:
        p *= Bcap(mu)
    return p


def gstep_factor(l) -> Fr:
    """base^11 · ∏Bcap / (W(5/3)^11) — the quantity Case2Property claims ≤ 1."""
    return baseOf(l) ** 11 * prodBcap(l) / DENOM


def margin(l) -> Fr:
    return 1 - gstep_factor(l)


def is_case2(l) -> bool:
    """base^11 > W(5/3)^11 — the Case-2 hypothesis (base above threshold)."""
    return baseOf(l) ** 11 > DENOM


# --- achievable messages (the integrality/achievability fact) -----------------
# The realizable child messages are NOT dense in (0,1].  A block's message is
# μ = 1/(j+1+S) with j = #children ≥ 0 and S = Σ child messages ≥ 0.  Hence:
#   * a LEAF (j=0, S=0) has μ = 1;
#   * every NON-LEAF (j ≥ 1) has μ = 1/(j+1+S) ≤ 1/(j+1) ≤ 1/2.
# So the achievable message set is  {1} ∪ (0, 1/2]  — there is a HARD GAP (1/2, 1)
# that the recursion cannot realize.  Verified by exact enumeration of all 16,755
# rooted vertices with n ≤ 10 (`envelope._collect_vertices`): the largest non-leaf
# message is 17/35 ≈ 0.4857 < 1/2, and none lies in (1/2, 1).
LEAF = Fr(1)                 # bare vertex child, F = W  (witnesses master_ub(1)=W)
ARM = Fr(1, 3)               # length-2 cherry child, F = 486/529 (witnesses glemma(1/3))
NONLEAF_MAX = Fr(1, 2)       # every non-leaf message ≤ 1/2 (the achievability constraint)


def is_achievable_message(mu: Fr) -> bool:
    """A message is achievable iff it is the leaf (μ=1) or lies in (0, 1/2]."""
    return mu == LEAF or (0 < mu <= NONLEAF_MAX)


@dataclass(frozen=True)
class GStepMarginReport:
    """Where the case-2 g-step margin bottoms out, and whether that point is an
    *achievable* config or a continuous phantom."""

    j_max: int = 8
    grid_Q: int = 240      # message-grid denominator for the continuous scan

    def continuous_scan(self):
        """Scan single-child (j=1) and symmetric multi-child case-2 configs over a
        fine *continuous* μ-grid.  Returns (min_margin, argmin_l, worst_over_one)
        where worst_over_one is the config with the LARGEST gstep_factor (most
        negative margin) — the continuous phantom, if any."""
        worst = None   # (margin, l)
        for j in range(1, self.j_max + 1):
            for p in range(1, self.grid_Q + 1):
                mu = Fr(p, self.grid_Q)          # μ ∈ (0, 1]
                l = [mu] * j
                if not is_case2(l):
                    continue
                m = margin(l)
                if worst is None or m < worst[0]:
                    worst = (m, l)
        return worst

    def achievable_scan(self):
        """Same scan but restricted to the ACHIEVABLE box: each non-leaf child
        message in (0, 1/2], plus any number of leaf children (μ=1).  This is what
        the recursion can actually realize; symmetric configs are the g_bound
        maximizers (branching_unimodality T1/T2) hence the margin-minimizers."""
        worst = None
        for j in range(0, self.j_max + 1):          # non-leaf children (symmetric)
            for k in range(0, self.j_max + 1):      # leaf children
                if j + k == 0:
                    continue
                for p in range(1, self.grid_Q // 2 + 1):
                    mu = Fr(p, self.grid_Q)          # μ ∈ (0, 1/2]
                    l = [mu] * j + [LEAF] * k
                    if not is_case2(l):
                        continue
                    m = margin(l)
                    if worst is None or m < worst[0]:
                        worst = (m, l)
        return worst

    def summary(self):
        cont = self.continuous_scan()
        ach = self.achievable_scan()
        return {
            "continuous_min_margin": cont[0],
            "continuous_argmin": cont[1],
            "continuous_violates": cont[0] < 0,
            "achievable_min_margin": ach[0],
            "achievable_argmin": ach[1],
            "achievable_violates": ach[0] < 0,
        }


# --- Step-2 per-child reduction (the Handelman-searchable target) --------------
#
# On the achievable box, the config-based g-step decomposes cleanly:
#
#  (1) SINGLE non-leaf child, glemma regime (μ ∈ [μ*, 1/2]):  the case-2 factor is
#          gstep([μ]) = W·((7+3μ)/(6+2μ))^11        (exact identity, verified)
#      and (7+3μ)/(6+2μ) is monotone increasing, so the box maximum is at μ=1/2,
#      i.e. 17/14 — the endpoint inequality  64·17^11 ≤ 621·14^11  IS the already
#      kernel-green `R3Cert.GStepCore.cert_j1`.  Single-child case: DONE, no new
#      certificate needed (elementary monotonicity + cert_j1).
#
#  (2) MULTI non-leaf children (j ≥ 2, μ_i ∈ (0,1/2]):  min margin ≈ +0.325 — a
#      strictly-positive-margin multivariate positivity, the genuine target for
#      `emit_handelman` / `emit_constrained_sos` (Putinar on the box [0,1/2]^j).
#
#  (3) LEAF children (μ=1): monotone-safe — adding leaves raises `base` but
#      multiplies by W < 1; the tight point is the single-leaf config = the ARM
#      (`l=[1]`, gstep = 1 exactly).
#
# The load-bearing correction: ALL of this needs the achievability hypothesis
# μ_nonleaf ≤ 1/2.  Without it the statement is FALSE (§ continuous_violates).

def single_child_reduced_ratio(mu: Fr) -> Fr:
    """The exact case-2 single-child factor in the glemma regime:
    W·((7+3μ)/(6+2μ))^11 = gstep([μ]).  Box-maximised at μ=1/2 (=cert_j1)."""
    return W * ((7 + 3 * mu) / (6 + 2 * mu)) ** 11


def cert_j1_holds() -> bool:
    """The single-child box endpoint: 64·17^11 ≤ 621·14^11 (R3Cert cert_j1)."""
    return 64 * 17 ** 11 <= 621 * 14 ** 11
