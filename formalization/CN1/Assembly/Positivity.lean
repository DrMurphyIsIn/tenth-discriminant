import OAI.NumberTheory.DirichletL.Nonvanishing
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Real-axis positivity of Dirichlet L-functions of real characters (step 5 of the argument)

Pinned environment: Lean v4.34.1, Mathlib d13f23b (the openai/math `OAI` root).

For a Dirichlet character `χ : DirichletCharacter ℂ N` whose values are fixed by complex
conjugation (`∀ a, conj (χ a) = χ a`; in particular every quadratic character, whose values lie
in `{-1, 0, 1}`), we prove:

1. `LFunction_conj`: the conjugation symmetry `L(χ, conj s) = conj (L(χ, s))` (away from the
   pole of the trivial character), by the identity principle from the termwise statement on
   `1 < re s`. Hence `LFunction_ofReal_im`: `L(χ, σ)` is real for real `σ`.
2. `LFunction_ofReal_re_pos_of_one_lt`: `L(χ, σ) > 0` for real `σ > 1`. The L-series tends to
   `χ(1) = 1` as `σ → ∞`, `L(χ, ·)` is real, continuous and non-vanishing on `(1, ∞)` (Mathlib's
   `LFunction_ne_zero_of_one_le_re`), so the sign is constant by the intermediate value theorem.
3. `LFunction_ofReal_re_pos_of_seven_eighths_lt`: for `χ ≠ 1`, `L(χ, σ) > 0` for every real
   `σ > 7/8`. Same argument, with OAI's zero-free region
   `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` in place of Mathlib's.
4. `LFunction_seven_eighths_nonneg`: for `χ ≠ 1`, `L(χ, 7/8)` is real and `≥ 0`, by continuity.

The only non-Mathlib input is OAI's theorem, used in 3 and 4; items 1 and 2 are Mathlib-only.
-/

set_option autoImplicit false

open Complex Set Filter Topology
open scoped ComplexConjugate

namespace CN1

open DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

omit [NeZero N] in
/-- A quadratic character (values in `{-1, 0, 1}`) is fixed by complex conjugation. -/
theorem _root_.MulChar.IsQuadratic.conj_apply (hq : χ.IsQuadratic) (a : ZMod N) :
    conj (χ a) = χ a := by
  rcases hq a with h | h | h <;> simp [h]

/-- Termwise conjugation symmetry of the L-series of a real character on `1 < re z`. -/
lemma conj_LFunction_conj_of_one_lt_re (hχ : ∀ a : ZMod N, conj (χ a) = χ a) {z : ℂ}
    (hz : 1 < z.re) : conj (LFunction χ (conj z)) = LFunction χ z := by
  rw [LFunction_eq_LSeries χ (by rwa [conj_re]), LFunction_eq_LSeries χ hz, LSeries, LSeries,
    conj_tsum]
  refine tsum_congr fun n ↦ ?_
  simp only [LSeries.term]
  split_ifs with hn
  · simp
  · rw [map_div₀, hχ, ← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]

/-- **Conjugation symmetry** of the L-function of a real Dirichlet character:
`L(χ, conj s) = conj (L(χ, s))`, for all `s` if `χ ≠ 1`, and for `s ≠ 1` if `χ = 1`. -/
theorem LFunction_conj (hχ : ∀ a : ZMod N, conj (χ a) = χ a) (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
    LFunction χ (conj s) = conj (LFunction χ s) := by
  -- the agreement on the open half-plane `1 < re z`, as an `EventuallyEq` at `2`
  have hev : (fun z ↦ conj (LFunction χ (conj z))) =ᶠ[𝓝 (2 : ℂ)] LFunction χ :=
    eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num))
      fun z hz ↦ conj_LFunction_conj_of_one_lt_re χ hχ hz
  rcases hs with hs | hχ1
  · -- `conj ∘ L ∘ conj` and `L` are analytic on the connected set `{1}ᶜ`
    have hg_an : AnalyticOnNhd ℂ (fun z ↦ conj (LFunction χ (conj z))) {1}ᶜ :=
      DifferentiableOn.analyticOnNhd
        (fun z hz ↦ (differentiableAt_conj_conj_iff.mpr <| differentiableAt_LFunction χ _ <|
          Or.inl ((map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hz)).differentiableWithinAt)
        isOpen_compl_singleton
    have hL_an : AnalyticOnNhd ℂ (LFunction χ) {1}ᶜ :=
      DifferentiableOn.analyticOnNhd
        (fun z hz ↦ (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt)
        isOpen_compl_singleton
    have heq : EqOn (fun z ↦ conj (LFunction χ (conj z))) (LFunction χ) {1}ᶜ :=
      hg_an.eqOn_of_preconnected_of_eventuallyEq hL_an
        (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
        (by norm_num : (2 : ℂ) ∈ _) hev
    simpa using congrArg (starRingEnd ℂ) (heq hs)
  · -- for `χ ≠ 1` both functions are entire
    have hg_an : AnalyticOnNhd ℂ (fun z ↦ conj (LFunction χ (conj z))) univ :=
      analyticOnNhd_univ_iff_differentiable.mpr
        fun z ↦ differentiableAt_conj_conj_iff.mpr (differentiable_LFunction hχ1 _)
    have hL_an : AnalyticOnNhd ℂ (LFunction χ) univ :=
      analyticOnNhd_univ_iff_differentiable.mpr (differentiable_LFunction hχ1)
    have heq := hg_an.eq_of_eventuallyEq hL_an hev
    simpa using congrArg (starRingEnd ℂ) (congrFun heq s)

/-- **Item 1.** The L-function of a real Dirichlet character is real on the real axis
(away from the pole of the trivial character). -/
theorem LFunction_ofReal_im (hχ : ∀ a : ZMod N, conj (χ a) = χ a) {σ : ℝ}
    (hσ : (σ : ℂ) ≠ 1 ∨ χ ≠ 1) : (LFunction χ σ).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← LFunction_conj χ hχ σ hσ, conj_ofReal]

/-- On the real axis, `L(χ, σ)` is the complex number given by its real part. -/
theorem LFunction_ofReal_eq_re (hχ : ∀ a : ZMod N, conj (χ a) = χ a) {σ : ℝ}
    (hσ : (σ : ℂ) ≠ 1 ∨ χ ≠ 1) : LFunction χ σ = ((LFunction χ σ).re : ℂ) :=
  Complex.ext (by simp) (by simp [LFunction_ofReal_im χ hχ hσ])

/-- If `L(χ, σ)` is real and non-zero, its real part is non-zero. -/
lemma LFunction_ofReal_re_ne_zero (hχ : ∀ a : ZMod N, conj (χ a) = χ a) {σ : ℝ}
    (hσ : (σ : ℂ) ≠ 1 ∨ χ ≠ 1) (h : LFunction χ σ ≠ 0) : (LFunction χ σ).re ≠ 0 := by
  intro hre
  apply h
  rw [LFunction_ofReal_eq_re χ hχ hσ, hre, ofReal_zero]

/-- `L(χ, x) → χ(1) = 1` as `x → ∞`; so `Re L(χ, x) > 0` at some real `x > 1`. -/
lemma exists_one_lt_and_LFunction_re_pos : ∃ x : ℝ, 1 < x ∧ 0 < (LFunction χ x).re := by
  have ha : LSeries.abscissaOfAbsConv (χ ·) < ⊤ :=
    lt_of_le_of_lt (LSeriesSummable_of_one_lt_re χ (s := 2) (by norm_num)).abscissaOfAbsConv_le
      (by simp)
  have ht : Tendsto (fun x : ℝ ↦ LSeries (χ ·) x) atTop (𝓝 1) := by
    have := LSeries.tendsto_atTop ha
    rwa [Nat.cast_one, map_one] at this
  have h2 : ∀ᶠ x : ℝ in atTop, 0 < (LSeries (χ ·) x).re :=
    ((Complex.continuous_re.tendsto 1).comp ht).eventually (lt_mem_nhds (by simp))
  obtain ⟨x, hx1, hx2⟩ := (h2.and (eventually_gt_atTop 1)).exists
  exact ⟨x, hx2, by rwa [LFunction_eq_LSeries χ (by simpa using hx2)]⟩

/-- Sign propagation: a continuous real function on a preconnected set, never zero there and
positive at one point, is positive everywhere on the set. -/
lemma pos_on_of_continuousOn_of_ne_zero {f : ℝ → ℝ} {S : Set ℝ} (hS : IsPreconnected S)
    (hf : ContinuousOn f S) (h0 : ∀ x ∈ S, f x ≠ 0) {a : ℝ} (ha : a ∈ S) (hpos : 0 < f a) :
    ∀ x ∈ S, 0 < f x := by
  intro x hx
  by_contra hneg
  have hlt : f x < 0 := lt_of_le_of_ne (not_lt.mp hneg) (h0 x hx)
  obtain ⟨y, hy, hy0⟩ := hS.intermediate_value hx ha hf ⟨hlt.le, hpos.le⟩
  exact h0 y hy hy0

/-- Continuity of `σ ↦ Re L(χ, σ)` at a real point away from the pole. -/
lemma continuousAt_LFunction_ofReal_re {σ : ℝ} (hσ : (σ : ℂ) ≠ 1 ∨ χ ≠ 1) :
    ContinuousAt (fun t : ℝ ↦ (LFunction χ t).re) σ :=
  Complex.continuous_re.continuousAt.comp
    ((differentiableAt_LFunction χ _ hσ).continuousAt.comp Complex.continuous_ofReal.continuousAt)

/-- **Item 2.** For a real Dirichlet character, `L(χ, σ) > 0` for every real `σ > 1`
(Mathlib-only: the L-series tends to `1`, and `L` is real, continuous and non-vanishing on
`(1, ∞)`). -/
theorem LFunction_ofReal_re_pos_of_one_lt (hχ : ∀ a : ZMod N, conj (χ a) = χ a) {σ : ℝ}
    (hσ : 1 < σ) : 0 < (LFunction χ σ).re := by
  obtain ⟨x, hx1, hxpos⟩ := exists_one_lt_and_LFunction_re_pos χ
  have hne : ∀ t : ℝ, 1 < t → (t : ℂ) ≠ 1 := fun t ht ↦ by exact_mod_cast ht.ne'
  refine pos_on_of_continuousOn_of_ne_zero (f := fun t : ℝ ↦ (LFunction χ t).re)
    isPreconnected_Ioi ?_ ?_ (mem_Ioi.mpr hx1) hxpos σ (mem_Ioi.mpr hσ)
  · exact fun t ht ↦ (continuousAt_LFunction_ofReal_re χ (Or.inl (hne t ht))).continuousWithinAt
  · intro t ht
    exact LFunction_ofReal_re_ne_zero χ hχ (Or.inl (hne t ht))
      (LFunction_ne_zero_of_one_le_re χ (Or.inr (hne t ht)) (by simpa using (le_of_lt ht)))

/-- **Item 3.** For a real non-trivial Dirichlet character, `L(χ, σ) > 0` for every real
`σ > 7/8`. Uses OAI's zero-free region `Re s > 7/8`. -/
theorem LFunction_ofReal_re_pos_of_seven_eighths_lt (hχ : ∀ a : ZMod N, conj (χ a) = χ a)
    (hχ1 : χ ≠ 1) {σ : ℝ} (hσ : 7 / 8 < σ) : 0 < (LFunction χ σ).re := by
  obtain ⟨x, hx1, hxpos⟩ := exists_one_lt_and_LFunction_re_pos χ
  have hx : (7 / 8 : ℝ) < x := by linarith
  refine pos_on_of_continuousOn_of_ne_zero (f := fun t : ℝ ↦ (LFunction χ t).re)
    isPreconnected_Ioi ?_ ?_ (mem_Ioi.mpr hx) hxpos σ (mem_Ioi.mpr hσ)
  · exact fun t _ ↦ (continuousAt_LFunction_ofReal_re χ (Or.inr hχ1)).continuousWithinAt
  · intro t ht
    exact LFunction_ofReal_re_ne_zero χ hχ (Or.inr hχ1)
      (OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ (s := t)
        (by simpa using (mem_Ioi.mp ht)) fun h ↦ hχ1 h.1)

/-- **Item 4.** For a real non-trivial Dirichlet character, `L(χ, 7/8)` is real and `≥ 0`
(by continuity from `σ > 7/8`). -/
theorem LFunction_seven_eighths_nonneg (hχ : ∀ a : ZMod N, conj (χ a) = χ a) (hχ1 : χ ≠ 1) :
    (LFunction χ (7 / 8)).im = 0 ∧ 0 ≤ (LFunction χ (7 / 8)).re := by
  have h78 : ((7 / 8 : ℝ) : ℂ) = 7 / 8 := by push_cast; ring
  rw [← h78]
  refine ⟨LFunction_ofReal_im χ hχ (Or.inr hχ1), ?_⟩
  have hc : ContinuousAt (fun t : ℝ ↦ (LFunction χ t).re) (7 / 8) :=
    continuousAt_LFunction_ofReal_re χ (Or.inr hχ1)
  refine ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (7 / 8)))) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (LFunction_ofReal_re_pos_of_seven_eighths_lt χ hχ hχ1 (mem_Ioi.mp ht)).le

/-! ### The same statements for quadratic characters (values in `{-1, 0, 1}`). -/

theorem LFunction_ofReal_im_of_isQuadratic (hq : χ.IsQuadratic) {σ : ℝ}
    (hσ : (σ : ℂ) ≠ 1 ∨ χ ≠ 1) : (LFunction χ σ).im = 0 :=
  LFunction_ofReal_im χ hq.conj_apply hσ

theorem LFunction_ofReal_re_pos_of_one_lt_of_isQuadratic (hq : χ.IsQuadratic) {σ : ℝ}
    (hσ : 1 < σ) : 0 < (LFunction χ σ).re :=
  LFunction_ofReal_re_pos_of_one_lt χ hq.conj_apply hσ

theorem LFunction_ofReal_re_pos_of_seven_eighths_lt_of_isQuadratic (hq : χ.IsQuadratic)
    (hχ1 : χ ≠ 1) {σ : ℝ} (hσ : 7 / 8 < σ) : 0 < (LFunction χ σ).re :=
  LFunction_ofReal_re_pos_of_seven_eighths_lt χ hq.conj_apply hχ1 hσ

theorem LFunction_seven_eighths_nonneg_of_isQuadratic (hq : χ.IsQuadratic) (hχ1 : χ ≠ 1) :
    (LFunction χ (7 / 8)).im = 0 ∧ 0 ≤ (LFunction χ (7 / 8)).re :=
  LFunction_seven_eighths_nonneg χ hq.conj_apply hχ1

end CN1

#print axioms CN1.LFunction_conj
#print axioms CN1.LFunction_ofReal_im
#print axioms CN1.LFunction_ofReal_re_pos_of_one_lt
#print axioms CN1.LFunction_ofReal_re_pos_of_seven_eighths_lt
#print axioms CN1.LFunction_seven_eighths_nonneg
#print axioms CN1.LFunction_seven_eighths_nonneg_of_isQuadratic
