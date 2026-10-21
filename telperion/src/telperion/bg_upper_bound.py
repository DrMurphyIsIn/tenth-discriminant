"""BG asymptotic upper bound — the composed reduction skeleton (2026-08-31).

This module assembles the whole branch-induction upper-bound argument into ONE explicit, machine-checkable
reduction: the goal `F(T) = (1/|T|) log pi(T) <= F* = log(621/64)/11` (asymptotically) is discharged by a
chain of steps, each tagged GATED (a kernel-gated certificate that `.check()`s here), BASE (a finite exhaustive
verification), BOUNDARY (an O(1) boundary constant, documented), LEMMA (proven elsewhere), or HYPOTHESIS (the
single open analytic input).  It is the honest "one lemma away" ledger in code -- `conjecture1_proved = False`.

The chain (see `docs/BG_UPPER_BOUND_REDUCTION_20260831.md`):

  [0] boundary        1 <= pi(T)/branch_total(T,r) <= 4/3, so (1/n)log pi <= F* + O(1/n) -> F*  GIVEN ell(B)<=0.
  [1] branch ceiling  ell(B) <= 0 for all rooted branches B, by induction on |B|:
        [1a] base      |B| <= 11 exhaustively verified.
        [1b] step      ell(hub of children c_i) <= ell(B(k)) [mixed<=broom] <= 0 [broom optimum].
  [2] mixed <= B(k)   the hub bound, split by root degree k:
        [2a] k >= 16   slack bound slack_g(k) <= F*                         GATED: TieSlackCertificate.
        [2b] k <= 15   concavity tangent + per-child KKT V(c_i) <= V(cherry):
              - brooms B(2..8)          GATED: MixedHubKKTCertificate.
              - d_c >= 7                GATED: HighDegreeTailCertificate.
              - d_c <= 6 non-broom      the M_d frontier bound, split into:
                  * near-broom finite   GATED: MdGeometricTailCertificate (peak arithmetic < threshold).
                  * near-broom unimodal GATED: NearBroomUnimodalityCertificate (peaks at m*, strictly decreases).
                  * extremality         the single-child lemma (SCL), now ASSEMBLED (2026-09-02):
                      - price flow       GATED: ExtremalityPriceMapCertificate (I=[456/3703,3/7] invariant).
                      - broom leg #4     GATED: BroomVsCherryOnICertificate (V_mu(B(d-1))<=V_mu(cherry) on I).
                      - leaf leg #5      GATED: LeafExchangeCertificate (leaf->cherry raises ell, d=3..6).
                      - assembly         GATED: SCLInductionCertificate (all legs consistent + price map closed on I).
                      - SCL induction    LEMMA: the well-founded recursion on |c| (as 1b; Lean = future work).
  [3] broom optimum   ell(B(k)) <= 0, = 0 iff k=5 (the 23-adic tie)        GATED: BroomOptimumCertificate.

EXTREMALITY assembly (2026-09-02): the last HYPOTHESIS (b) -- the single-child lemma `V_mu(c) <= V_mu(cherry)` on
the invariant price interval `I=[456/3703,3/7]` -- is discharged by strong induction on `|c|` (price map keeps `I`
invariant; concave-log tangent decouples a degree-`d<=6` hub into per-child inequalities at the child price
`mu'' in I`; child cases leaf [#5, excluded] / broom `B(m<=5)` [#4] / degree `>=7` [HighDegreeTail] / non-broom
degree `<=6` [IH]).  All arithmetic legs are now GATED (norm_num certificates, #4 with log-enclosures, #5 pure
rational `(3(4d-1)/(2(4d+1)))^11 > 621/64`; `SCLInductionCertificate` re-checks their mutual consistency + that
the price map is closed on `I`).  The SINGLE remaining open input (b) is thereby reduced from "assemble + prove
the extremality" to purely the WELL-FOUNDED RECURSION on `|c|` -- a Lean induction proof analogous to the
branch-ceiling induction (1b).  `conjecture1_proved = False`: the recursion Lean formalization is future work, and
the FULL conjecture also needs the finite-`n` structural side (tree->hub / Hnorm-Hdom) and the matching lower
bound (`S(k,5)` achieves `F*`).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Optional

from .spider_broom import BroomOptimumCertificate
from .tie_regime import (
    BroomVsCherryOnICertificate, ExtremalityPriceMapCertificate, HighDegreeTailCertificate,
    LeafExchangeCertificate, MdGeometricTailCertificate, MixedHubKKTCertificate,
    NearBroomUnimodalityCertificate, SCLInductionCertificate, TieSlackCertificate,
)

GATED, BASE, BOUNDARY, LEMMA, HYPOTHESIS = "GATED", "BASE", "BOUNDARY", "LEMMA", "HYPOTHESIS"


@dataclass(frozen=True)
class ReductionStep:
    """One step of the upper-bound reduction.  `kind` in {GATED, BASE, BOUNDARY, LEMMA, HYPOTHESIS}; `cert` is a
    callable returning a certificate with `.check()` for GATED steps (else `None`)."""

    tag: str
    statement: str
    kind: str
    cert: Optional[Callable[[], object]] = None

    def verify(self) -> Optional[bool]:
        """`True/False` for GATED steps (does the certificate check?); `None` for non-gated steps."""
        if self.kind != GATED or self.cert is None:
            return None
        return bool(self.cert().check())


@dataclass(frozen=True)
class UpperBoundReduction:
    """The composed BG asymptotic-upper-bound reduction.  `.steps` is the full chain; `.verify_gated()` checks
    every GATED certificate; `.open_hypotheses()` returns the open analytic inputs (exactly one: the small-degree
    refined ceiling (b)).  `conjecture_proved` is `False` iff any step is a HYPOTHESIS -- and it is."""

    steps: tuple = field(default_factory=tuple)

    @staticmethod
    def build() -> "UpperBoundReduction":
        return UpperBoundReduction(steps=(
            ReductionStep("0", "1 <= pi(T)/branch_total(T,r) <= 4/3  =>  (1/n)log pi <= F* + O(1/n)  [given ell<=0]",
                          BOUNDARY),
            ReductionStep("1a", "branch ceiling base: ell(B) <= 0 for |B| <= 11 (exhaustive)", BASE),
            ReductionStep("1b", "branch ceiling step: ell(hub of c_i) <= ell(B(k)) <= 0 (induction on |B|)", LEMMA),
            ReductionStep("2a", "mixed <= B(k), k >= 16: slack_g(k) <= F*", GATED, TieSlackCertificate),
            ReductionStep("2b-brooms", "mixed <= B(k), k <= 15: per-child V(B(j)) < V(cherry), B(2..8)",
                          GATED, MixedHubKKTCertificate),
            ReductionStep("2b-hi", "envelope tail, d_c >= 7: V(c) < V(cherry) via ceiling ell<=0",
                          GATED, HighDegreeTailCertificate),
            ReductionStep("2b-lo-fin", "M_d finite arithmetic: near-broom peaks d=2..5 + d=6 boundary < threshold",
                          GATED, MdGeometricTailCertificate),
            ReductionStep("2b-lo-unimodal", "near-broom family (d-2)cherries+B(m) peaks at m*=max(1,d-3) & strictly "
                          "decreases after (BIG^11 < (621/64)^2 + Handelman monotone tail) -- UNCONDITIONAL, no rho",
                          GATED, NearBroomUnimodalityCertificate),
            ReductionStep("2b-lo-pricemap", "extremality price-flow: the single-child lemma's joint size-induction "
                          "keeps prices in the invariant interval I=[456/3703,3/7] (concavity-tangent map)",
                          GATED, ExtremalityPriceMapCertificate),
            ReductionStep("2b-lo-bvc", "extremality leg #4: reference broom V_mu(B(d-1)) <= V_mu(cherry) on I "
                          "(both endpoints, brooms deg<=6; margin +0.012)",
                          GATED, BroomVsCherryOnICertificate),
            ReductionStep("2b-lo-leaf", "extremality leg #5: leaf->cherry raises ell for d in 3..6 "
                          "((3(4d-1)/(2(4d+1)))^11 > 621/64), so bare leaves never occur in the argmax",
                          GATED, LeafExchangeCertificate),
            ReductionStep("2b-lo-assembly", "SCL induction arithmetic backbone: every leg (price-map, tangent gap 0, "
                          "broom-vs-cherry, leaf-exchange, hi-degree, near-broom) consistent + price map closed on I",
                          GATED, SCLInductionCertificate),
            ReductionStep("2b-lo-scl-induction", "SCL Lean-formalized in R3Cert.BGSCLInduction (no `sorry`, local "
                          "lake build green): the concrete SCL V_mu(b)<=V_mu(cherry) for EVERY branch is REDUCED "
                          "(scl_of_step) to ONE per-hub inequality SCLStep -- recursion, concrete cavity total/ell/"
                          "h/y/V_mu + positivity, ell recursion (bell_node), concave tangent (log_tangent/"
                          "bell_node_tangent), hub y-formula (bY_node) all proven. Remaining: discharge SCLStep = "
                          "the price-flow decouple (mu->mu''=3[(4d-1)-3mu]/(4d-1)^2 over I) + hbroom (gated leg #4 "
                          "un-cleared by log-monotonicity) = the hard BG inequality itself, i.e. the leaf-free "
                          "near-broom argmax extremality (leaves excluded via leaf_le_cherry at mu''<=3/11)",
                          HYPOTHESIS),
            ReductionStep("3", "broom optimum: ell(B(k)) <= 0, = 0 iff k=5 (23-adic tie)",
                          GATED, BroomOptimumCertificate),
        ))

    def verify_gated(self) -> dict:
        """`{tag: bool}` for every GATED step -- all must be `True` for the gated skeleton to hold."""
        return {s.tag: s.verify() for s in self.steps if s.kind == GATED}

    def gated_ok(self) -> bool:
        return all(self.verify_gated().values())

    def open_hypotheses(self) -> list:
        """The open analytic inputs (HYPOTHESIS steps).  Exactly one: the small-degree refined ceiling (b)."""
        return [s for s in self.steps if s.kind == HYPOTHESIS]

    @property
    def conjecture_proved(self) -> bool:
        """`False` while any HYPOTHESIS remains open (it does -- (b))."""
        return len(self.open_hypotheses()) == 0

    def status(self) -> str:
        from collections import Counter
        c = Counter(s.kind for s in self.steps)
        gated = self.verify_gated()
        return (f"gated={sum(gated.values())}/{len(gated)} pass; "
                f"steps: " + ", ".join(f"{k}={c[k]}" for k in (GATED, BASE, BOUNDARY, LEMMA, HYPOTHESIS) if c[k])
                + f"; open hypotheses={len(self.open_hypotheses())}; conjecture_proved={self.conjecture_proved}")


conjecture1_proved = False
