import CN1.ChowlaSelberg.SevenEighths

/-!
# HCN.CS.Slice: the Poisson slice for a scaled, shifted Gaussian

The generalisation of CN-1's `CN1.CS.slice` (PoissonSlice.lean) from the principal form to any slice
`q(x) = A (x + α)² + Y/π` with `A > 0`, `Y > 0` and a real shift `α`:

  `Σ_x q(x)^{-s} = π^s/Γ(s) · A^{-1/2} Σ_k e^{2πikα} I(s; Y, πk²/A)`   (`re s > 1`).

For `q(x) = Q(x, y) = a x² + b x y + c y²` (`y ≠ 0`) this is the general slice, with `A = a`, `α = by/(2a)`,
`Y = π D y²/(4a)` and the phase `e^{2πik·by/(2a)}` in place of CN-1's sign. The proof is CN-1's, with the theta
transformation (`CN1.CS.theta_shift`) applied at `A t` instead of `t`. This module declares no interface definition of
`HCN.Statements.GeneralCS`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Real
open CN1.CS

namespace HCN.CSAux

/-- `A^{-1/2} = (√A)⁻¹` as a complex power, for `A > 0`. -/
lemma cpow_neg_half {A : ℝ} (hA : 0 < A) : (A : ℂ) ^ (-(1 / 2 : ℂ)) = (((Real.sqrt A)⁻¹ : ℝ) : ℂ) := by
  rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hA.le,
    Real.rpow_neg hA.le, Real.sqrt_eq_rpow]

/-- The phase `e^{2πikα}` (real `α`) is a unit complex number. -/
lemma norm_cexp_two_pi_I_mul (k : ℤ) (α : ℝ) : ‖cexp (2 * π * Complex.I * k * α)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- Theta with a scale: `Σ_n e^{-π (A t)(n + α)²} = A^{-1/2} t^{-1/2} Σ_k e^{-(πk²/A)/t} e^{2πikα}`. -/
theorem theta_shift_scaled {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (α : ℝ) :
    ∑' n : ℤ, (Real.exp (-(π * (A * t)) * ((n : ℝ) + α) ^ 2) : ℂ) =
      (((Real.sqrt A)⁻¹ : ℝ) : ℂ) * ((t : ℂ) ^ (-(1 / 2 : ℂ)) *
        ∑' k : ℤ, (Real.exp (-(π * (k : ℝ) ^ 2 / A) / t) : ℂ) * cexp (2 * π * Complex.I * k * α)) := by
  rw [theta_shift (mul_pos hA ht) α]
  have e1 : ((A * t : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = (A : ℂ) ^ (-(1 / 2 : ℂ)) * (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
    push_cast
    exact mul_cpow_ofReal_nonneg hA.le ht.le _
  rw [e1, cpow_neg_half hA, mul_assoc]
  congr 2
  refine tsum_congr fun k => ?_
  rw [show -(π * (k : ℝ) ^ 2) / (A * t) = -(π * (k : ℝ) ^ 2 / A) / t by ring]

/-- **The general Poisson slice.** If `π q(x) = π A (x + α)² + Y` with `A, Y > 0`, `B_k = πk²/A`, and
`Σ_x q(x)^{-re s}` converges (`re s > 1`), then
`Σ_x q(x)^{-s} = π^s/Γ(s) · A^{-1/2} Σ_k e^{2πikα} I(s; Y, B_k)`. -/
theorem slice_gen {A α Y : ℝ} (hA : 0 < A) (hY : 0 < Y) {q : ℤ → ℝ}
    (hq : ∀ x : ℤ, π * q x = π * A * ((x : ℝ) + α) ^ 2 + Y) {Bk : ℤ → ℝ}
    (hB : ∀ k : ℤ, Bk k = π * (k : ℝ) ^ 2 / A) {s : ℂ} (hs : 1 < s.re)
    (hsum : Summable fun x : ℤ => q x ^ (-s.re)) :
    ∑' x : ℤ, (q x : ℂ) ^ (-s) =
      (π : ℂ) ^ s / Gamma s * ((((Real.sqrt A)⁻¹ : ℝ) : ℂ) *
        ∑' k : ℤ, cexp (2 * π * Complex.I * k * α) * I s Y (Bk k)) := by
  have hs0 : 0 < s.re := by linarith
  have hs2 : 1 / 2 < s.re := by linarith
  have hqpos : ∀ x : ℤ, 0 < q x := by
    intro x
    have h : 0 < π * q x := by rw [hq x]; positivity
    exact pos_of_mul_pos_right h Real.pi_pos.le
  have hB0 : ∀ k : ℤ, 0 ≤ Bk k := fun k => by rw [hB]; positivity
  -- Step 1: each term as a Gamma integral.
  have step1 : ∀ x : ℤ, (q x : ℂ) ^ (-s) = (π : ℂ) ^ s / Gamma s * mellin (kern (π * q x) 0) s :=
    fun x => cpow_neg_eq_mellin (hqpos x) hs0
  simp_rw [step1]
  rw [tsum_mul_left]
  congr 1
  -- Step 2: exchange sum and integral in `x`.
  have hF_int : ∀ x : ℤ, Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * kern (π * q x) 0 t)
      (volume.restrict (Ioi 0)) :=
    fun x => integrableOn_cpow_mul_kern (by have := hqpos x; positivity) le_rfl hs0
  have hF_sum : Summable fun x : ℤ =>
      ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * kern (π * q x) 0 t‖ := by
    have hsum' := hsum.mul_left (Real.Gamma s.re * π⁻¹ ^ s.re)
    refine hsum'.congr fun x => ?_
    have hx := hqpos x
    have e : ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * kern (π * q x) 0 t‖ =
        ∫ t : ℝ in Ioi 0, t ^ (s.re - 1) * Real.exp (-((π * q x) * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp ht), sub_re, one_re,
        norm_kern, zero_div, add_zero]
    rw [e, Real.integral_rpow_mul_exp_neg_mul_Ioi hs0 (by positivity), one_div, mul_inv,
      Real.mul_rpow (inv_nonneg.mpr Real.pi_pos.le) (inv_nonneg.mpr hx.le),
      Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
    ring
  unfold mellin
  simp_rw [smul_eq_mul]
  rw [integral_tsum_of_summable_integral_norm hF_int hF_sum]
  -- Step 3: the `k`-side, as an integral of a sum.
  have hCn : ‖((((Real.sqrt A)⁻¹ : ℝ) : ℂ))‖ = (Real.sqrt A)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hG_int : ∀ k : ℤ, Integrable
      (fun t : ℝ => (((Real.sqrt A)⁻¹ : ℝ) : ℂ) * (cexp (2 * π * Complex.I * k * α) *
        ((t : ℂ) ^ (s - 3 / 2) * kern Y (Bk k) t)))
      (volume.restrict (Ioi 0)) :=
    fun k => ((integrableOn_I_integrand hY (hB0 k) hs2).const_mul _).const_mul _
  have hG_sum : Summable fun k : ℤ =>
      ∫ t : ℝ in Ioi 0, ‖(((Real.sqrt A)⁻¹ : ℝ) : ℂ) * (cexp (2 * π * Complex.I * k * α) *
        ((t : ℂ) ^ (s - 3 / 2) * kern Y (Bk k) t))‖ := by
    have hc : 0 < Real.sqrt (Y * (π / A)) := Real.sqrt_pos.mpr (by positivity)
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
      (fun k => ?_) ((summable_exp_neg_mul_abs_int hc).mul_left
        ((Real.sqrt A)⁻¹ * ((2 / Y) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2))))
    have hn : ∀ t : ℝ, ‖(((Real.sqrt A)⁻¹ : ℝ) : ℂ) * (cexp (2 * π * Complex.I * k * α) *
        ((t : ℂ) ^ (s - 3 / 2) * kern Y (Bk k) t))‖ =
        (Real.sqrt A)⁻¹ * ‖(t : ℂ) ^ (s - 3 / 2) * kern Y (Bk k) t‖ := fun t => by
      rw [norm_mul, norm_mul, hCn, norm_cexp_two_pi_I_mul, one_mul]
    simp_rw [hn]
    rw [integral_const_mul]
    have hsq : Real.sqrt (Y * Bk k) = Real.sqrt (Y * (π / A)) * |(k : ℝ)| := by
      rw [hB, show Y * (π * (k : ℝ) ^ 2 / A) = (Y * (π / A)) * (k : ℝ) ^ 2 by ring,
        Real.sqrt_mul (by positivity) ((k : ℝ) ^ 2), Real.sqrt_sq_eq_abs]
    calc (Real.sqrt A)⁻¹ * ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 3 / 2) * kern Y (Bk k) t‖
        ≤ (Real.sqrt A)⁻¹ * (Real.exp (-Real.sqrt (Y * Bk k)) *
            ((2 / Y) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2))) :=
          mul_le_mul_of_nonneg_left (integral_norm_I_integrand_le hY (hB0 k) hs2) (by positivity)
      _ = _ := by rw [hsq]; ring
  simp_rw [I_eq_integral, ← integral_const_mul]
  rw [← tsum_mul_left]
  simp_rw [← integral_const_mul]
  rw [integral_tsum_of_summable_integral_norm hG_int hG_sum]
  -- Step 4: pointwise identity of the integrands, via the scaled theta transformation.
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : 0 < t := mem_Ioi.mp ht
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hk : ∀ x : ℤ, kern (π * q x) 0 t =
      (Real.exp (-(π * (A * t)) * ((x : ℝ) + α) ^ 2) : ℂ) * (Real.exp (-(Y * t)) : ℂ) := by
    intro x
    rw [kern, ← ofReal_mul, ← Real.exp_add]
    congr 2
    have := hq x
    rw [zero_div, add_zero]
    linear_combination (-t) * this
  simp_rw [hk]
  rw [tsum_mul_left, tsum_mul_right, theta_shift_scaled hA ht α]
  rw [show ∀ X : ℂ, (t : ℂ) ^ (s - 1) * ((((Real.sqrt A)⁻¹ : ℝ) : ℂ) * ((t : ℂ) ^ (-(1 / 2 : ℂ)) * X) *
      (Real.exp (-(Y * t)) : ℂ)) = ((t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
        (((Real.sqrt A)⁻¹ : ℝ) : ℂ) * (Real.exp (-(Y * t)) : ℂ)) * X from fun X => by ring]
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hT : (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-(1 / 2 : ℂ)) = (t : ℂ) ^ (s - 3 / 2) := by
    rw [← cpow_add _ _ ht0]
    congr 1
    ring
  have hk' : kern Y (Bk k) t =
      (Real.exp (-(Y * t)) : ℂ) * (Real.exp (-(π * (k : ℝ) ^ 2 / A) / t) : ℂ) := by
    rw [kern, ← ofReal_mul, ← Real.exp_add, hB]
    congr 2
    ring
  rw [hk', hT]
  ring

end HCN.CSAux
