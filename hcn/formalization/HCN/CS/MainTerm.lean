import CN1.ChowlaSelberg.SevenEighths

/-!
# HCN.CS.MainTerm: the `y = 0` slice and the `k = 0` terms, for a general form

* `tsum_a_sq_cpow`: `Σ_x (a x²)^{-s} = a^{-s} · 2ζ(2s)` (`re s > 1/2`), the `y = 0` slice of `a x² + b x y + c y²`;
* `I_zero_term_gen`, `tsum_I_zero_gen`, `summable_I_zero_gen`: with `A_y = α y²`, the `k = 0` terms
  `I(s; α y², 0) = Γ(s - 1/2) (1/α)^{s - 1/2} (y²)^{1/2 - s}` sum over `y ≠ 0` to `Γ(s - 1/2) (1/α)^{s - 1/2} · 2ζ(2s - 1)`
  (`re s > 1`). For the general form `1/α = 4a/(πD)`.

CN-1's MainTerm.lean (`tsum_int_sq_cpow`, `I_zero_term`, `tsum_I_zero`) with `π d/4` replaced by a general `α > 0`. This
module declares no interface definition of `HCN.Statements.GeneralCS`.
-/

open Complex Set
open scoped Real
open CN1.CS

namespace HCN.CSAux

/-- The `y = 0` slice: `Σ_x (a x²)^{-s} = a^{-s} · 2ζ(2s)` for `a > 0`, `re s > 1/2`. -/
theorem tsum_a_sq_cpow {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 1 / 2 < s.re) :
    ∑' x : ℤ, ((a * (x : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) = (a : ℂ) ^ (-s) * (2 * riemannZeta (2 * s)) := by
  have h : ∀ x : ℤ, ((a * (x : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) = (a : ℂ) ^ (-s) * (((x : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) :=
    fun x => by rw [Complex.ofReal_mul]; exact mul_cpow_ofReal_nonneg ha.le (sq_nonneg _) _
  simp_rw [h]
  rw [tsum_mul_left, tsum_int_sq_cpow hs]

variable {α : ℝ}

/-- The `k = 0` term for `y ≠ 0` (and `0` for `y = 0`), in closed form. -/
lemma I_zero_term_gen (hα : 0 < α) {s : ℂ} (hs : 1 / 2 < s.re) (y : ℤ) :
    (if y = 0 then 0 else I s (α * (y : ℝ) ^ 2) 0) =
      Gamma (s - 1 / 2) * ((α⁻¹ : ℝ) : ℂ) ^ (s - 1 / 2) * (((y : ℝ) ^ 2 : ℝ) : ℂ) ^ (-(s - 1 / 2)) := by
  have hs0 : s - 1 / 2 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  split_ifs with hy
  · subst hy
    have h0 : (((0 : ℤ) : ℝ) ^ 2 : ℝ) = 0 := by simp
    rw [h0, Complex.ofReal_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0), mul_zero]
  · have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have hy2 : 0 < (y : ℝ) ^ 2 := by positivity
    have e : (1 / ((α * (y : ℝ) ^ 2 : ℝ) : ℂ)) = ((α⁻¹ * ((y : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
      push_cast
      field_simp
    rw [I_zero (by positivity) hs, e, cpow_mul_ofReal (inv_pos.mpr hα) (inv_pos.mpr hy2),
      cpow_inv_ofReal hy2]
    ring

theorem tsum_I_zero_gen (hα : 0 < α) {s : ℂ} (hs : 1 < s.re) :
    ∑' y : ℤ, (if y = 0 then 0 else I s (α * (y : ℝ) ^ 2) 0) =
      Gamma (s - 1 / 2) * ((α⁻¹ : ℝ) : ℂ) ^ (s - 1 / 2) * (2 * riemannZeta (2 * s - 1)) := by
  have hs' : 1 / 2 < s.re := by linarith
  simp_rw [I_zero_term_gen hα hs']
  rw [tsum_mul_left, tsum_int_sq_cpow (by simp; linarith)]
  congr 3
  ring

lemma summable_I_zero_gen (hα : 0 < α) {s : ℂ} (hs : 1 < s.re) :
    Summable fun y : ℤ => (if y = 0 then 0 else I s (α * (y : ℝ) ^ 2) 0) := by
  have hs' : 1 / 2 < s.re := by linarith
  simp_rw [I_zero_term_gen hα hs']
  refine Summable.mul_left _ ?_
  have hw0 : s - 1 / 2 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have h2w : 1 < (2 * (s - 1 / 2)).re := by simp; linarith
  have hf : Summable fun n : ℕ => (((n : ℝ) ^ 2 : ℝ) : ℂ) ^ (-(s - 1 / 2)) := by
    simp_rw [sq_cpow_eq_one_div _ hw0]; exact Complex.summable_one_div_nat_cpow.mpr h2w
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨hf.congr fun n => by simp, hf.congr fun n => by simp⟩

end HCN.CSAux
