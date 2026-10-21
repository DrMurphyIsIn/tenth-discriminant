# Zeta Zero Localization -- Honest Status (ALL ZEROS UP TO HEIGHT 100 ON THE LINE)

conjecture1_proved = False.

**HEADLINE (dVP + box combination, concrete T=100 certificate):** the Lean theorem
`AllZeros_h100.all_nontrivial_zeros_up_to_height_100`
(`examples/zeta_zero_localization/lean/AllZeros_h100.lean`) is kernel-verified:
**ALL nontrivial zeros of the Riemann zeta function up to height 100 lie on
`Re s = 1/2`** -- a complete finite Turing verification, kernel-checked. Axioms:
{propext, Classical.choice, Quot.sound}.  No sorryAx.  It is **NOT** a proof of the
Riemann Hypothesis.

This CLOSES the earlier "verified inside a box" framing into "verified up to a
HEIGHT": it composes two kernel atoms at the concrete instance `a = 1/10^6`, `T = 100`:

* **Confinement (dVP + FE):** `ZetaZeroConfinement.zero_in_band` puts every nontrivial
  zero up to height 100 inside the band `[1/10^6, 1 - 1/10^6]`.  Derived from the
  SELF-CONTAINED **effective** de la Vallee Poussin zero-free region (PR #316/#318 --
  `dlvpRateC` is a concrete closed-form constant, so **the earlier non-effective-c
  caveat is REMOVED**) plus the functional equation.  The effective-rate edge
  `1/10^6 <= dlvpRateC / log 100` is discharged in-kernel here (`AllZeros_h100.haC_100`)
  via explicit rational `Real.exp`/`Real.log` enclosures.
* **Box-localization (argument principle + winding):** the emitted wide-box atom
  `RHInBox_1d1000000_999999d1000000_0_100.rh_in_box_1d1000000_999999d1000000_0_100`
  (box `[1/10^6, 1 - 1/10^6] x [0, 100]`, winding `N == N_line == 29`) puts every
  zeta zero in that box on `Re s = 1/2`.

**Trust boundary (honest).**  KERNEL: the dVP zero-free region + functional equation
(confinement), the argument principle + winding-integral algebra (box), and the
`haC` rate inequality.  ARB NON-KERNEL INPUT: the winding count `N = 29`, the 29
on-line zeros (`hLine`), the edge non-vanishing + integrability bundle (`hArb`), and
the height floor `55/16 <= |Im|` for nontrivial zeros up to 100 (`hγ`).  These are
outward-rounded python-flint/Arb ball certificates carried as documented hypotheses.

**`hγ` residual (route c).**  Mathlib has no "no nontrivial zeros below height 55/16
(~3.44)" fact, so the region's height floor is carried as the documented non-kernel
hypothesis `hγ` on `all_nontrivial_zeros_up_to_height_100` -- a classical
Arb-certifiable fact (the on-line sweep places all 29 zeros at height >= 14).  The
headline is thus honestly "all zeros up to 100 on Re = 1/2, given no nontrivial zeros
below height 55/16".  conjecture1_proved = False.

---


**Headline (Stage 3, Task 6):** the Lean theorem
`BoxLocalization.all_nontrivial_zeros_in_box_on_critical_line`
(`examples/zeta_zero_localization/lean/BoxLocalization.lean`) is kernel-verified:
EVERY nontrivial zero of the Riemann zeta function in the box
`B = [2/5, 3/5] x [10, 35]` lies on the critical line `Re s = 1/2` (and is
simple).  This is a Turing-style **VERIFICATION of RH INSIDE THIS BOX**.  It is
**NOT** a proof of the Riemann Hypothesis.  The winding integer (= 5), edge
non-vanishing, and value enclosures are Arb-certified NON-KERNEL input (the same
trust boundary as Stage 1's enclosures); the kernel proves every implication
(per-segment FTC, the box argument principle, the Blaschke split with in-kernel
E-holomorphicity, and this localization/counting exhaustion).  Axioms:
{propext, Classical.choice, Quot.sound}.  No sorryAx.

## What is kernel-proven

The Lean theorem `XiLineZeros.lambda_five_zeros_10_35` (in
`examples/zeta_zero_localization/lean/XiLineZeros.lean`) states:

    Given 10 real enclosure hypotheses (the sign-definite Arb-certified bounds
    on gLine(t) at the 10 anchor sample points), there exist 5 strictly
    increasing reals x1 < x2 < x3 < x4 < x5 in [10, 35] with
    completedRiemannZeta(1/2 + x_k * I) = 0 for each k in 1..5.

This is kernel-verified by Lean 4 / Mathlib with axioms:
    {propext, Classical.choice, Quot.sound}
No sorryAx.  No placeholders.

Because Lambda's zeros are exactly the nontrivial zeros of the Riemann zeta
function (Lambda = pi^(-s/2) * Gamma(s/2) * zeta(s) has no other zeros), the
theorem LOCATES 5 nontrivial zeros of zeta on the critical line Re s = 1/2 in
the interval [10, 35].  The 5 located zeros match the 5 known nontrivial zeros:
    t ~ 14.1347, 21.0220, 25.0109, 30.4249, 32.9351.

This is the first kernel-verified on-line nontrivial-zero count for the
Riemann zeta function.

## Kernel-proven sub-lemmas (in LambdaLineReal.lean)

- `ZetaZeroLocalization.completedRiemannZeta₀_conj`: conjugation symmetry of the
  entire part Lambda_0.
- `ZetaZeroLocalization.completedRiemannZeta_conj`: conjugation symmetry of Lambda.
- `ZetaZeroLocalization.completedZeta_im_eq_zero`: Lambda(1/2 + t*I) is real for
  all t in R (proved via the functional equation Lambda(1-s) = Lambda(s) and the
  fact that conj(1/2 + t*I) = 1 - (1/2 + t*I)).

These three lemmas together establish the "real on the line" prelude that all
sign-change arguments consume.

## Arb-certified non-kernel input boundary

The 10 enclosure hypotheses in the MILESTONE theorem are the boundary between the
kernel-verified proof and the external oracle:

    henc8:  gLine 14     <= -(large negative rational)     -- Re Lambda < 0
    henc9:  (large positive rational) <= gLine (29/2)      -- Re Lambda > 0
    henc22: (large positive rational) <= gLine 21          -- Re Lambda > 0
    henc23: gLine (43/2) <= -(...)                         -- Re Lambda < 0
    henc30: gLine 25     <= -(...)                         -- Re Lambda < 0
    henc31: (...)        <= gLine (51/2)                   -- Re Lambda > 0
    henc40: (...)        <= gLine 30                       -- Re Lambda > 0
    henc41: gLine (61/2) <= -(...)                         -- Re Lambda < 0
    henc45: gLine (65/2) <= -(...)                         -- Re Lambda < 0
    henc46: (...)        <= gLine 33                       -- Re Lambda > 0

These are produced by `telperion.arb_enclosure.enclose_lambda` at 300-bit Arb
precision.  The rational endpoints are exact fractions.Fraction derived via
man_exp outward-rounded dyadic arithmetic from the Arb ball's midpoint and
radius.  Arb ball arithmetic is internally certified (interval arithmetic with
outward rounding), but Lean does not independently verify the constant's value.

The theorem is valid for ANY assignment of the function gLine satisfying the
hypotheses.  The enclosure hypotheses are the oracle boundary -- a user who
independently verifies them (by any means) gets the kernel-certified zero-existence
conclusion unconditionally from the Lean proof.

## What this does NOT prove

- It does NOT prove the Riemann Hypothesis.  RH asserts all nontrivial zeros lie
  on Re s = 1/2.  This theorem locates specific zeros ON the line from certified
  enclosures; it says nothing about zeros that might lie off the line.
  conjecture1_proved = False.

- It does NOT give an exact zero count in [10, 35].  The lower bound N >= 5 comes
  from odd sign changes (each sign change certifies at least one zero via IVT).
  The exact count requires computing the argument principle integral -- Stage 2.

- It does NOT prove that these are ALL the nontrivial zeros in [10, 35].  There
  could be additional zeros between the sampled sign-change subintervals (e.g. a
  pair of zeros that do not produce a net sign change with 0.5 spacing).

## Stage roadmap

- Stage 1 (COMPLETE): lower bound N >= 5 via sign changes + IVT.  This file.
- Stage 2B (COMPLETE, Task 7): the LOCAL Blaschke split of `zeta'/zeta` over the
  box B = [2/5, 3/5] x [10, 35] is KERNEL-DERIVED (see below).
- Stage 2 (COMPLETE, Task 5/7/9): exact zero count = 5 via the box argument
  principle (`BoxArgPrincipleZeta.box_arg_principle_zeta'`), with the winding
  integer (= 5) the Arb-certified input and the split + E-holomorphy
  kernel-derived.
- Stage 3 (COMPLETE, Task 6): RH-in-a-box -- ALL nontrivial zeros in
  B = [2/5, 3/5] x [10, 35] lie on Re s = 1/2.  Achieved NOT by a global
  off-line zero-free region but by a COUNTING EXHAUSTION: total divisor = 5
  (argument principle) and 5 distinct on-line zeros (Stage 1, bridged
  completedRiemannZeta <-> riemannZeta) force the support to be exactly those 5
  on-line simple zeros.  See below.

## Stage 2B: kernel-derived local Blaschke split (Task 7)

`BlaschkeBox.zeta_blaschke_split_box`
(`examples/zeta_zero_localization/lean/BlaschkeBox.lean`) DERIVES, in kernel, the
local principal-part split of `logDeriv riemannZeta` over the capstone box.  On
the open ball `U = ball(cB, 13)` (center `cB = 1/2 + (45/2) i`, radius 13) that
contains the closed box `B = [2/5, 3/5] x [10, 35]` and excludes zeta's only pole
`s = 1`, there is a finite set `s` of zeta zeros in `U`, the divisor `d`, and an
error `E` such that:

    at every z in U with zeta z != 0,
      logDeriv zeta z = (sum_{rho in s} (d rho)/(z - rho)) + E z,
    and E is HOLOMORPHIC on B  (DifferentiableOn C E B).

Mechanism: zeta is analytic on `{1}^c` (`analyticOn_riemannZeta`), hence
meromorphic on `U`; `divisor_ball_support_finite` (compact `closedBall`) gives a
finite divisor support; `MeromorphicOn.extract_zeros_poles` yields an analytic,
zero-free remainder `g` on `U` with `zeta =(codiscrete) (prod (.-u)^(d u)) * g`;
an in-file identity-principle transfer (`logDeriv_congr_of_codiscrete`, a
reproduction of the `zero_free_bridge/DlvpTransfer` germ lemmas) moves the
codiscrete factorization to a POINTWISE `logDeriv` identity on `U`; the finite
product's `logDeriv` is the residue sum, and `E := logDeriv g` is holomorphic on
`U` (hence on `B`) because `g` is analytic and non-vanishing.

Axioms: {propext, Classical.choice, Quot.sound}.  No sorryAx.

This DISCHARGES Task 5's H2 (E-holomorphy), previously a hypothesis.
`BoxArgPrincipleZeta.box_arg_principle_zeta`
(`examples/zeta_zero_localization/lean/BoxArgPrincipleZeta.lean`) instantiates the
capstone with the derived `E, s, d` and the kernel E-holomorphy; the four
per-segment boundary split identities (H1) are DERIVED from the kernel split, so
the only residual boundary input is that the four edges carry no zeta zero
(`hnz_*`) -- the SAME Arb-enclosure trust boundary as the numeric zero
enclosures, carried as named documented hypotheses (NOT faked).  Strict
interiority (H3), routine boundary integrability, and the winding value (H4, from
WindingCount / Task 9) remain the other inputs.

conjecture1_proved = False.

## Stage 3: RH-in-a-box localization capstone (Task 6)

`BoxLocalization.all_nontrivial_zeros_in_box_on_critical_line`
(`examples/zeta_zero_localization/lean/BoxLocalization.lean`) composes the three
kernel results into: every nontrivial zeta zero in `B = [2/5, 3/5] x [10, 35]`
lies on `Re s = 1/2`, and is simple.

Ingredients (all kernel unless noted):

1. TOTAL COUNT = 5.  `BoxArgPrincipleZeta.box_arg_principle_zeta` gives
   `sum_{rho in s} d rho = 5`, where `s` is the ACTUAL divisor support of zeta on
   the ball `U = ball(cB, 13) contains B` and `d = MeromorphicOn.divisor` its
   multiplicity.  The winding integer `N = 5`, edge non-vanishing, strict
   interiority, and value enclosures are the Arb-certified NON-KERNEL inputs
   (bundled as `hArb`, applied to the KERNEL divisor witnesses so the split and
   E-holomorphy are NOT among the residual inputs).

2. DIVISOR FACTS (kernel, added to `BlaschkeBox.zeta_blaschke_split_box`): zeta
   is analytic on `U` (no poles), so `d rho >= 1` at every support point, and
   every zeta zero in `U` lies in `s` (its analytic order is >= 1 != 0).

3. LAMBDA <-> ZETA BRIDGE (kernel, `zeta_zero_iff_completed_zero`): on `B`,
   `Re > 0`, so `Gammaℝ s != 0` and `riemannZeta s = completedRiemannZeta s /
   Gammaℝ s`; hence the two functions share zeros.  Stage 1's 5 distinct on-line
   completedRiemannZeta zeros ARE 5 distinct on-line riemannZeta zeros in `B`,
   each in the support `s`.

4. COUNTING EXHAUSTION (kernel, `exhaustion_by_count` + `box_localization_core`):
   the 5 distinct on-line zeros form `T subset s` with `|T| = 5`, each `d >= 1`,
   and `sum_s d = 5`.  A Finset sum-split (`Finset.sum_sdiff`) forces `s = T` and
   every `d rho = 1`.  Therefore any zeta zero in `B` is one of the 5 on-line
   zeros -- so `Re = 1/2` and simple.

Axioms: {propext, Classical.choice, Quot.sound}.  No sorryAx.  An
`example : <exact type> := ...` gate pins the capstone's statement.

Emitter / negative control: `src/telperion/emit_box_localization.py` provides the
`box_localization` certificate and the `BoxLocalizationEmitter` (kind
`box_localization`, STRUCTURALLY_NONVACUOUS).  The certificate REFUSES
`n_line > n_total` (impossible -- more on-line zeros than the total count) and
`n_line != n_total` (no exhaustion without equality), so a fabricated instance
with an off-line zero (making `n_total = 6 > n_line = 5`) cannot emit a
localization claim.  This negative control also runs in
`examples/zeta_zero_localization/generate.py --check`.

conjecture1_proved = False.  This VERIFIES RH inside the box; it is NOT a proof
of RH.

## Parameterized generic theorem + T=100 milestone (Tasks 3-5)

The capstone above is specialized to `[2/5, 3/5] x [10, 35]`.  Tasks 3-5
generalize it to an ARBITRARY box and extend the verified RANGE up to height 100
(Turing's method) -- still NOT a proof of RH.

GENERIC THEOREM (Task 3, kernel).  `RHInBox.rh_in_box_of_certificate`
(`lean/RHInBox.lean`, layered over `RHInBoxCore.lean` and `RHInBoxAnalytic.lean`)
takes, for a box `[s0, s1] x [t0, t1]`, a chosen Blaschke ball `(c, R)` with the
box strictly inside and the pole `s = 1` strictly outside, a count `N`, and the
two documented Arb inputs (`hLine`: `N` strictly-Im-increasing on-line zeros;
`hArb`: boundary non-vanishing/integrability bundle + winding `= 2*pi*I*N`), and
concludes: every nontrivial zeta zero in the box lies on `Re s = 1/2`.  The
implication is entirely kernel; winding `N`, edge non-vanishing, and value
enclosures remain the Arb-certified NON-KERNEL input.

DRIVER (Task 4).  `examples/zeta_zero_localization/generate.py --box s0,s1,t0,t1`
(and the shortcut `--height T` for `[2/5, 3/5] x [0, T]`) computes, for the box,
the rigorous boundary winding `N`, the on-line sign-change count `N_line`, and
edge non-vanishing, REFUSES any box that excludes `1/2`, contains the pole, or has
`N_line != N`, and emits a standalone Lean file instantiating the generic theorem.

MILESTONE (Task 5).  `--height 100` certifies the box `[2/5, 3/5] x [0, 100]`
with winding `N == N_line == N(100) = 29` (the 29 on-line nontrivial zeros of
zeta up to height 100) and emits the COMMITTED file
`lean/RHInBox_2d5_3d5_0_100.lean` (theorem `rh_in_box_2d5_3d5_0_100`), registered
as a permanent `lean_lib`.  It builds sorry-free with axioms
{propext, Classical.choice, Quot.sound}.  This is a kernel-certified
**VERIFICATION of RH INSIDE `[2/5, 3/5] x [0, 100]`** -- it extends the verified
RANGE beyond the earlier `[10, 35]` box, and is NOT a proof of the Riemann
Hypothesis.  conjecture1_proved = False.

Scale note: the emitted instantiation proof is `O(N^2)` in a pairwise-distinctness
block (N=29 -> 406 pairs), and each `linarith` slows as the context grows, so the
whole proof is super-quadratic.  The emitter therefore scales
`set_option maxHeartbeats` with `N` (default for `N <= 10`; `~8.6M` at `N = 29`).
Observed at height 100: emit ~1.8 s; `lake build` ~5m45s (single Lean file) on
top of a warm Mathlib cache.

## Proof mechanism

For each sign-change subinterval [t_i, t_k] (t_i < t_k, gLine(t_i) and
gLine(t_k) have opposite signs):

1. The enclosure hypothesis pins the sign at each endpoint (hi < 0 for a
   negative box, lo > 0 for a positive box).
2. gLine is continuous (completedRiemannZeta is differentiable away from {0,1};
   1/2 + t*I is never 0 nor 1; continuity of Re follows).
3. The intermediate value theorem (intermediate_value_Icc or
   intermediate_value_Icc') yields a root r in [t_i, t_k].
4. The root is strictly interior: r = t_i would make gLine(r) = 0 at an endpoint
   where gLine is nonzero (contradiction); same for r = t_k.
5. Consecutive roots are strictly increasing: r_{m+1} < t_{k_m} <= t_{i_next} <
   r_{m+2} (the gap t_{k_m} <= t_{i_next} is a rational literal comparison
   discharged by norm_num).  The subintervals may be adjacent (t_{k_m} =
   t_{i_next}) or separated by straddling samples (t_{k_m} < t_{i_next}); the
   <= covers both, so distinctness holds either way.
6. lambda_eq_gLine (proved from completedZeta_im_eq_zero) rewrites
   completedRiemannZeta(1/2 + r*I) = gLine(r) promoted to C; gLine(r) = 0 gives
   the zero.

## Files

    examples/zeta_zero_localization/generate.py        -- interval driver + emitter
    examples/zeta_zero_localization/lean/LambdaLineReal.lean  -- Task 2 prelude
    examples/zeta_zero_localization/lean/XiLineZeros.lean     -- emitted theorems
    examples/zeta_zero_localization/lean/BlaschkeBox.lean     -- Task 7: kernel-derived local Blaschke split (+ d>=1, zeros-in-s)
    examples/zeta_zero_localization/lean/BoxArgPrincipleZeta.lean -- Task 7: box argument principle for zeta (H1+H2 discharged)
    examples/zeta_zero_localization/lean/BoxLocalization.lean -- Task 6: STAGE 3 CAPSTONE (RH-in-a-box localization)
    examples/zeta_zero_localization/lean/RHInBoxCore.lean     -- Task 3: generic RH-in-box core
    examples/zeta_zero_localization/lean/RHInBoxAnalytic.lean -- Task 3: generic analytic layer
    examples/zeta_zero_localization/lean/RHInBox.lean         -- Task 3: generic rh_in_box_of_certificate
    examples/zeta_zero_localization/lean/RHInBox_2d5_3d5_0_100.lean -- T=100 box milestone ([2/5,3/5]x[0,100], N=29), COMMITTED
    examples/zeta_zero_localization/lean/ZetaZeroConfinement.lean -- CONFINEMENT (dVP+FE): zeros up to T in band [a,1-a]
    examples/zeta_zero_localization/lean/AllZerosUpToHeight.lean -- COMBINATION (generic a,T): all zeros up to T on Re=1/2
    examples/zeta_zero_localization/lean/RHInBox_1d1000000_999999d1000000_0_100.lean -- WIDE-box atom ([1/10^6,1-1/10^6]x[0,100], N=29), COMMITTED
    examples/zeta_zero_localization/lean/AllZeros_h100.lean -- CONCRETE T=100 certificate: ALL zeros up to height 100 on Re=1/2, COMMITTED
    tests/test_dvp_box.py                              -- build assertions (confinement, generic, concrete T=100) + wide-box N==N_line==29 agreement
    examples/zeta_zero_localization/README.md          -- usage + cert boundary doc
    src/telperion/arb_enclosure.py                     -- Task 1: enclose_lambda
    src/telperion/emit_xi_line_zeros.py                -- sign_change_count + emitter
    src/telperion/emit_box_localization.py             -- Task 6: box_localization emitter + negative control
    tests/test_zeroloc_end_to_end.py                   -- TDD gate: N >= 5 on [10,35]
    tests/test_xi_line_zeros.py                        -- emitter unit tests
    tests/test_box_localization.py                     -- Task 6: capstone emit-shape + refusal tests
