import Mathlib

/-!
# HCN.CS.Mono: the inequality behind `Bg_mono`

`F(a) = (√a)⁻¹ (8a/(πD))^{3/8} · e^{-c}/(1 - e^{-c})²`, `c = π√D/(2a)`, is increasing in `a` as long as
`c(a') ≥ 1/8` at the larger point `a'`. Write `a' = a t⁸` with `t ≥ 1`. The prefactor scales by `t³/t⁴ = 1/t`; the
denominator `(1 - e^{-c})²` only helps (`c` decreases); and `t e^{-c} ≤ e^{-c'}`, because
`c - c' = c'(t⁸ - 1) ≥ (t⁸ - 1)/8 ≥ t - 1` (Bernoulli) and `e^{c - c'} ≥ 1 + (c - c')`. This is the
criterion `d/da log Bg > 0 ⟺ c(1 + 2e^{-c}/(1 - e^{-c})) > 1/8`, without derivatives. On `a' ≤ (2/3)√D`, `c' ≥ 3π/4 > 1/8`.

This module declares no interface definition of `HCN.Statements.GeneralCS`.
-/

open scoped Real

namespace HCN.CSAux

theorem bg_core_mono {a a' D : ℝ} (hD : 0 < D) (ha : 0 < a) (haa' : a ≤ a')
    (hc' : 1 / 8 ≤ π * Real.sqrt D / (2 * a')) :
    (Real.sqrt a)⁻¹ * (8 * a / (π * D)) ^ (3 / 8 : ℝ) *
      (Real.exp (-(π * Real.sqrt D / (2 * a))) / (1 - Real.exp (-(π * Real.sqrt D / (2 * a)))) ^ 2) ≤
    (Real.sqrt a')⁻¹ * (8 * a' / (π * D)) ^ (3 / 8 : ℝ) *
      (Real.exp (-(π * Real.sqrt D / (2 * a'))) / (1 - Real.exp (-(π * Real.sqrt D / (2 * a')))) ^ 2) := by
  have ha' : 0 < a' := lt_of_lt_of_le ha haa'
  have hr : 1 ≤ a' / a := (one_le_div ha).mpr haa'
  obtain ⟨t, ht1, ht8⟩ : ∃ t : ℝ, 1 ≤ t ∧ t ^ 8 = a' / a :=
    ⟨(a' / a) ^ (1 / 8 : ℝ), Real.one_le_rpow hr (by norm_num), by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num⟩
  have ht0 : 0 < t := by linarith
  have ha'eq : a' = a * t ^ 8 := by rw [ht8]; field_simp
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsqrt : Real.sqrt a' = Real.sqrt a * t ^ 4 := by
    rw [ha'eq, Real.sqrt_mul ha.le, show t ^ 8 = (t ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hpow : (8 * a' / (π * D)) ^ (3 / 8 : ℝ) = (8 * a / (π * D)) ^ (3 / 8 : ℝ) * t ^ 3 := by
    rw [ha'eq, show 8 * (a * t ^ 8) / (π * D) = (8 * a / (π * D)) * t ^ 8 by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  rw [hsqrt, hpow]
  set C := π * Real.sqrt D / (2 * a) with hC
  set C' := π * Real.sqrt D / (2 * a') with hC'
  have hCC : C = C' * t ^ 8 := by
    rw [hC, hC', ha'eq]
    field_simp
  have hC'pos : 0 < C' := by linarith
  have ht8' : 1 ≤ t ^ 8 := one_le_pow₀ ht1
  have hle : C' ≤ C := by rw [hCC]; nlinarith
  have hbern : 1 + ((8 : ℕ) : ℝ) * (t - 1) ≤ (1 + (t - 1)) ^ 8 := one_add_mul_le_pow (by linarith) 8
  have hdiff : t - 1 ≤ C - C' := by
    have hb : (1 : ℝ) + 8 * (t - 1) ≤ t ^ 8 := by
      have := hbern; push_cast at this; simpa using this
    rw [hCC]
    nlinarith
  have hexp : t * Real.exp (-C) ≤ Real.exp (-C') := by
    have h1 : t ≤ Real.exp (C - C') := by linarith [Real.add_one_le_exp (C - C')]
    calc t * Real.exp (-C) ≤ Real.exp (C - C') * Real.exp (-C) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (-C') := by rw [← Real.exp_add]; ring_nf
  have hq' : 0 < 1 - Real.exp (-C') := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hC'pos); linarith
  have hqq : 1 - Real.exp (-C') ≤ 1 - Real.exp (-C) := by
    have := Real.exp_le_exp.mpr (neg_le_neg hle); linarith
  have hK : 0 ≤ (Real.sqrt a)⁻¹ * (8 * a / (π * D)) ^ (3 / 8 : ℝ) := by positivity
  have hfrac : Real.exp (-C) / (1 - Real.exp (-C)) ^ 2 ≤
      Real.exp (-C') / (1 - Real.exp (-C')) ^ 2 / t := by
    rw [le_div_iff₀ ht0]
    calc Real.exp (-C) / (1 - Real.exp (-C)) ^ 2 * t = t * Real.exp (-C) / (1 - Real.exp (-C)) ^ 2 := by
          ring
      _ ≤ Real.exp (-C') / (1 - Real.exp (-C)) ^ 2 :=
          div_le_div_of_nonneg_right hexp (by positivity)
      _ ≤ Real.exp (-C') / (1 - Real.exp (-C')) ^ 2 :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) (pow_le_pow_left₀ hq'.le hqq 2)
  calc (Real.sqrt a)⁻¹ * (8 * a / (π * D)) ^ (3 / 8 : ℝ) * (Real.exp (-C) / (1 - Real.exp (-C)) ^ 2)
      ≤ (Real.sqrt a)⁻¹ * (8 * a / (π * D)) ^ (3 / 8 : ℝ) *
          (Real.exp (-C') / (1 - Real.exp (-C')) ^ 2 / t) :=
        mul_le_mul_of_nonneg_left hfrac hK
    _ = (Real.sqrt a * t ^ 4)⁻¹ * ((8 * a / (π * D)) ^ (3 / 8 : ℝ) * t ^ 3) *
          (Real.exp (-C') / (1 - Real.exp (-C')) ^ 2) := by
        field_simp

/-- On `0 < a' ≤ (2/3)√D`, `c' = π√D/(2a') ≥ 3π/4 ≥ 1/8`. -/
lemma one_eighth_le_cst {a' D : ℝ} (ha' : 0 < a') (ha'D : a' ≤ 2 / 3 * Real.sqrt D) :
    1 / 8 ≤ π * Real.sqrt D / (2 * a') := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [Real.pi_gt_three]

end HCN.CSAux
