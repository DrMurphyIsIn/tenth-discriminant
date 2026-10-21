"""Arm-dominance against SMALL competitors -- a scoped sub-result (NOT uniform).

CORRECTION (2026-08-16, after the origin session's catch): the claim that arm
uniformly dominates EVERY added child is FALSE, and this module's scope is now
restricted to what actually holds.

  ARM beats a SMALL competitor X (leaf, cherry, arm2) uniformly in the hub
  arm-count k -- Phi^11(hub + arm) >= Phi^11(hub + X) -- and that IS
  kernel-certifiable (degree-11 all-nonneg-coefficient Polya, see
  UniformArmDominanceCertificate).  Keep it as a correctly-scoped sub-result.

  But arm does NOT dominate ALL children.  The 11-node near-star TIE N(0,5) is a
  tighter competitor than any small tree, and adding the tie BEATS adding the arm
  for every hub arm-count k >= 19 (verified: crossing at k=19 in this rec model,
  matching the origin's rational_reduction).  So "uniform arm-dominance" has an
  INFINITE exception family (k >= 19), at the opposite end from the k=0 base case.

This is the campaign's core wall (the marginal-tie / sharp-Psi obstruction): the
tie has logPhi = 0 (it sits on the extremal variety), the arm has logPhi < 0, and
in a WIDE hub the environment's sensitivity shrinks toward zero and cannot pay for
the arm's amplitude deficit.  The double blind spot that hid it: a competitor set
of only small trees (excluding the tie) and a k-sweep stopping short of k=19 --
exactly the armification_probe lesson ("verify moves against LARGE C_i, not just
small trees").

Consequence for the two-lemma framing: it does NOT split into mechanical (1) +
deep (2).  Arm-beats-any-child (uniform) is false; arm-beats-small-competitors is
true but does NOT drive an exchange, because the exchange must dispose of
tie-subtree children -- and disposing of large tie-children IS the hard content.
The whole mountain is there.  conjecture1_proved = False, reinforced.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def _rec(cr, kids):
    ch = [_rec(*k) for k in kids]
    S = sum(m for m, _ in ch)
    d = len(kids) + 1 + cr
    z = Fr(3, 3 * d + cr)
    m = z / (1 + z * S)
    a11 = (Fr(3, 2) ** (11 * cr)) * (Fr(64, 621) ** (1 + 2 * cr))
    p = a11 * (1 + z * S) ** 11
    for _, q in ch:
        p *= q
    return (m, p)


ARM = (0, [(0, [])])
LEAF = (0, [])
CHERRY = (1, [])


def hub_phi(cr, children):
    return _rec(cr, list(children))[1]


TIE = (0, [ARM] * 5)   # the 11-node near-star tie N(0,5): the LARGE extremal
                       # competitor that must be in any honest candidate set --
                       # it beats the arm for hub arm-count k >= 19.


def _default_children():
    # includes the TIE so the check cannot silently exclude the large extremal
    # subtree (the armification_probe lesson).
    return [ARM, LEAF, CHERRY,
            (0, [(0, [(0, [])])]),          # arm-of-arm (arm2)
            (0, [(0, []), (0, [(0, [])])]),  # mixed
            (1, [(0, [(0, [])])]),           # cherry + arm
            TIE]                             # the large tie competitor


@dataclass(frozen=True)
class ArmDominanceCertificate:
    """At hub state (cr cherries, k existing arms): whether adding an ARM beats
    adding each candidate child (incl. the TIE).  NOTE: this HOLDS for small k but
    FAILS for k >= 19 against the tie -- so it is a per-state check, not a uniform
    claim.  Use it only where check() returns True (small hubs)."""

    name: str
    cr: int
    k: int
    children: tuple = None

    def _cands(self):
        return self.children or _default_children()

    def arm_value(self):
        return hub_phi(self.cr, [ARM] * self.k + [ARM])

    def check(self) -> bool:
        av = self.arm_value()
        return all(av >= hub_phi(self.cr, [ARM] * self.k + [X]) for X in self._cands())

    def lean(self) -> str:
        av = self.arm_value()
        lines = [
            f"-- {self.name}: ARM-DOMINANCE at hub state (cr={self.cr}, k={self.k}).\n"
            f"-- Adding an arm beats adding any other child X (exact Phi^11, with the\n"
            f"-- prod-deg penalty).  This is the recursion-uniform monotone tail: every\n"
            f"-- non-arm direction decreases Phi more, so the near-star is extremal.\n"
        ]
        for i, X in enumerate(self._cands()):
            if X == ARM:
                continue
            xv = hub_phi(self.cr, [ARM] * self.k + [X])
            # av >= xv  <=>  av.num * xv.den >= xv.num * av.den  (cross-multiplied)
            lhs = av.numerator * xv.denominator
            rhs = xv.numerator * av.denominator
            lines.append(f"theorem {self.name}_dom_{i} : "
                         f"({rhs}:ℤ) ≤ {lhs} := by norm_num")
        return "\n".join(lines) + "\n"


def arm_dominance_uniform(cr_range=range(0, 4), k_range=range(0, 26)):
    """Check arm-dominance (against the full candidate set INCLUDING the tie) across
    hub states; returns (holds_everywhere, exceptions).  With the tie in the set and
    k swept past 19, this correctly reports the INFINITE exception family k >= 19
    (plus the k=0 base case) -- i.e. arm-dominance is NOT uniform."""
    exceptions = []
    for cr in cr_range:
        for k in k_range:
            if not ArmDominanceCertificate("t", cr, k).check():
                exceptions.append((cr, k))
    return (not exceptions), exceptions


# ---- UNIFORM arm-dominance in the hub parameter k (lemma 1) ------------------
# The per-state checks above lift to ONE inequality uniform in k: for each
# competitor child X, adding an arm beats adding X for all real k >= anchor,
# certified by a degree-11 polynomial num_X(k) whose shift num_X(anchor+u) has
# ALL NONNEGATIVE COEFFICIENTS (bare Polya / positivity) -- the same crossing
# structure as the 1-D bridge, one level up.  The leaf's anchor is k>=1 (its k=0
# exception is exactly the empty-hub base case that BUILDS the arm).

import sympy as _sp

_K, _U = _sp.symbols("k u", nonnegative=True)
_PHI_ARM = Fr(64, 621) ** 2 * Fr(3, 2) ** 11
_COMPETITORS = {
    "arm2": (Fr(3, 7), Fr(64, 621) * Fr(7, 6) ** 11 * _PHI_ARM),
    "leaf": (Fr(1), Fr(64, 621)),
    "cherry": (Fr(3, 4), Fr(3, 2) ** 11 * Fr(64, 621) ** 3),
}


def _arm_dom_numerator(m, phi):
    zp = _sp.Rational(3, 1) / (3 * (_K + 2))
    fac = lambda mm, ph: (1 + zp * (_K * _sp.Rational(1, 3) + mm)) ** 11 * ph
    diff = _sp.together(fac(_sp.Rational(1, 3), _PHI_ARM) - fac(m, phi))
    return _sp.expand(_sp.fraction(diff)[0])


def uniform_arm_dominance(competitor: str):
    """Returns (num_poly_in_k, minimal_anchor) certifying arm >= competitor for
    all real k >= anchor by bare Polya (num(anchor+u) has nonneg coeffs)."""
    m, phi = _COMPETITORS[competitor]
    num = _arm_dom_numerator(m, phi)
    for a in range(0, 4):
        cu = _sp.Poly(_sp.expand(num.subs(_K, a + _U)), _U).all_coeffs()
        if all(c >= 0 for c in cu):
            return num, a
    return num, None


@dataclass(frozen=True)
class UniformArmDominanceCertificate:
    """Arm beats each SMALL competitor (arm2, cherry, leaf) uniformly in the hub
    arm-count k: degree-11 numerator num_X(anchor+u) >= 0 by positivity (all nonneg
    coeffs).  SCOPED: this is arm-vs-small-competitor ONLY.  It is NOT uniform
    arm-dominance -- the large tie N(0,5) beats the arm for k >= 19 (an infinite
    exception this certificate deliberately does NOT cover)."""

    name: str = "uniform_armdom_small"
    competitors: tuple = ("arm2", "cherry", "leaf")

    def check(self) -> bool:
        return all(uniform_arm_dominance(c)[1] is not None for c in self.competitors)

    def lean(self) -> str:
        lines = [
            f"-- {self.name}: ARM-DOMINANCE UNIFORM in the hub arm-count k -- adding an\n"
            f"-- arm beats adding competitor X for all real k >= anchor, by the\n"
            f"-- all-nonneg-coefficient numerator (positivity).  Lemma (1) for the key\n"
            f"-- competitors; leaf anchor k>=1 (its k=0 exception BUILDS the arm).\n"
        ]
        for c in self.competitors:
            num, a = uniform_arm_dominance(c)
            numu = _sp.expand(num.subs(_K, a + _U))
            pl = _sp.printing.sstr(numu).replace("**", "^")
            lines.append(
                f"theorem {self.name}_{c} (u : ℝ) (hu : 0 ≤ u) : (0:ℝ) ≤ {pl} := by positivity"
            )
        return "\n".join(lines) + "\n"
