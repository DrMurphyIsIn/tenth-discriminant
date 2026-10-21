# Recipe — Monotone-fixpoint cap-decoupling (analytic-rate optimizations)

**What it solves.** In dVP / zero-free-region / any analytic-*rate* proof you optimize a width `σ`
that is defined as a decreasing function of a scale `L`, e.g.

    σ = 1 + 1/(2(3A + 5·A·L))          (σ ↓ as L ↑)

yet `σ` also appears *inside the very bounds that determine `L`* — the numeric constraint you must
satisfy is

    C / den(σ) + Bg(σ)  ≤  A·L          with  den(σ) = R − ‖z₀(σ)‖ ,  ‖z₀(σ)‖ = 2 − σ .

Defining `L` from the actual `C/den(σ) + Bg(σ)` is circular (`L → σ → den,Bg → L`). This recipe
breaks the loop. It is the pattern behind
`examples/zero_free_bridge/lean/DlvpZetaConcreteClose.lean:dlvp_zeta_region_concrete`.

**The move (three steps).**

1. **Separate what is σ-dependent from what is not.** Often the count `C` is *already*
   σ-independent (it is a fixed geometric/analytic quantity of the disk — a divisor finsum, a Jensen
   count). Only the *geometric factor* in `Bg(σ)` moves with σ. Isolate it.

2. **Cap the σ-dependent factor by a σ-independent endpoint value.** Because `σ ∈ (1, 1 + 1/(cA)]`
   pins `‖z₀‖ = 2 − σ ∈ [·, 1)`, the geometric factor is bounded by its `z₀ → 1` endpoint:

       (R + ‖z₀‖) / (R − ‖z₀‖)²  ≤  (R + 1) / (R − 1)²  =: geometric cap   (σ-independent)

   ⟹ `Bg(σ) ≤ Bgcap` and `den(σ) = R − ‖z₀‖ ≥ R − 1 > 0`, so `C/den(σ) ≤ |C|/(R−1)`. Both RHS are
   σ-independent. This endpoint cap is now a first-class Telperion emitter:
   **`endpoint_geom_cap`** (`emit_endpoint_geom_cap.py`, kind `endpoint_geom_cap`, in the
   `dvp_geom_atoms` example) — `(R+z)/(R−z)² ≤ (R+1)/(R−1)²` for `z ≤ 1`, `R > 1`, proof `gcongr`.

3. **Define `L` from the caps, let `σ` fall out.** Set

       L := 1 + 1/(A·ε) + (|C|/(R−1) + Bgcap)/A                    (σ-independent, ≥ 1)

   then **define** `σ := 1 + 1/(2(3A + 5·A·L))` as an *output*. Now `A·L ≥ |C|/(R−1) + Bgcap ≥
   C/den(σ) + Bg(σ)` gives the numeric constraint with no circularity, and `den(σ) > R − 1 > 0`,
   `σ ≤ 2`, `σ > 1` all follow from `σ ∈ (1, 1 + 1/(cA)]`.

**Companion move — non-explicit-neighborhood inputs (the pole).** When an input holds only
`∀ᶠ s in 𝓝[≠] a, P s` (e.g. Mathlib's `log_deriv_riemannZeta_add_inv_sub_bounded`), extract a radius
`ε` (`eventually_iff_exists_mem` → `Metric.mem_nhdsWithin_iff` gives `ball a ε ∩ {a}ᶜ ⊆ t`) and add a
`1/(A·ε)` term to `L` so that `σ − 1 = 1/(2(3A+5AL)) < ε`; then `P` holds at the real point `σ`.
Because `ε` is non-explicit, the resulting theorem is existential in the scale (`∃ A L`), i.e. the
rate constant is **non-effective** — exactly as dVP's constant classically is.

**Lean hygiene (learned the hard way).**
- `clear_value` *every* large `set`-var (`A, R, C, Bgcap, L, σ, Bg`) immediately after its `set … with
  h`. Otherwise tactics unfold the (huge, nested) values and you hit `whnf`/`isDefEq` heartbeat
  timeouts. You keep the equation `h` for `rw`; you lose only the (unwanted) defeq unfolding.
- The whole assembly is one big theorem ⟹ raise `set_option maxHeartbeats` (1_200_000 sufficed).
  This does **not** affect kernel-cleanliness (`#print axioms` stays `[propext, Classical.choice,
  Quot.sound]`).
- For the `∃`-rate form you do **not** need a Jensen `O(log|γ|)` bound on `C`: take `C := ↑(∑ᶠ …)`
  (the actual count) so `hC` is `le_refl`. You only need the log RATE if you additionally want to
  assert `β ≤ 1 − c/log|γ|` (that needs an *upper* bound `C ≤ K·log|γ|` too).

**When to reach for it.** Any "choose the scale to dominate a bounded-numerator-over-bounded-
denominator plus a bounded term, where the width sits inside the bounds" — dVP regions, Borel–
Carathéodory rate optimizations, iterated-bound fixpoints.

conjecture1_proved = False.
