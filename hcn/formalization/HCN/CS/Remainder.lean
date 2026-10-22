import CN1.ChowlaSelberg.SevenEighths

/-!
# HCN.CS.Remainder: a generic Chowla–Selberg remainder and its SHARP bound

The generic remainder term `T u A Bk s (y, k) = u(k, y) · I(s; A_y, B_k)` for `y ≠ 0`, `k ≠ 0` (and `0` otherwise),
with a unit phase `‖u‖ = 1`, `A_y = α y²` and `B_k = β k²` (`α, β > 0`). The interface `HCN.CS.Rtermg` is the case
`u = phase a b`, `α = π D/(4a)`, `β = π/a`, where `√(αβ) = π√D/(2a) = cstg a D` and `2/α = 8a/(πD)`. This module
declares no interface definition of `HCN.Statements.GeneralCS`.

Main facts, with `c = √(αβ)`:
* `norm_T_le`: `‖T s p‖ ≤ Γ(σ - 1/2) (2/α)^{σ - 1/2} · e^c e^{-c|y|} e^{-c|k|}` (`re s = σ > 1/2`), from CN-1's
  `norm_I_le`, `√(A_y B_k) = c|y||k|`, and the SHARP split `|y||k| ≥ |y| + |k| - 1`, i.e. `(|y| - 1)(|k| - 1) ≥ 0`
  (CN-1's `norm_Rterm_le` uses the weaker `|y||k| ≥ (|y| + |k|)/2`);
* `norm_tsum_T_le`: `‖Σ T s p‖ ≤ Γ(σ - 1/2) (2/α)^{σ - 1/2} · 4e^{-c}/(1 - e^{-c})²`, since
  `e^c (Σ_{n ≠ 0} e^{-c|n|})² = e^c (2e^{-c}/(1 - e^{-c}))² = 4e^{-c}/(1 - e^{-c})²`;
* `differentiableOn_tsum_T`: `s ↦ Σ T s p` is holomorphic on `re s > 1/2`;
* `tsum_T_ofReal_im`: if `conj u(k, y) = u(-k, y)` and `B_{-k} = B_k`, then `Σ T σ p` is real for real `σ`
  (pair `k ↔ -k`);
* `tsum_u_I_split`: the `k = 0` term of a slice separated from the `T`-terms.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Real
open CN1.CS

namespace HCN.CSAux

/-- The generic remainder term `u(k, y) I(s; A_y, B_k)`, and `0` if `y = 0 ∨ k = 0`. -/
noncomputable def T (u : ℤ → ℤ → ℂ) (A Bk : ℤ → ℝ) (s : ℂ) (p : ℤ × ℤ) : ℂ :=
  if p.1 = 0 ∨ p.2 = 0 then 0 else u p.2 p.1 * I s (A p.1) (Bk p.2)

/-- The product majorant `e^c e^{-c|y|} e^{-c|k|}` (`0` on the axes). -/
noncomputable def maj (c : ℝ) (p : ℤ × ℤ) : ℝ := Real.exp c * (gmaj c p.1 * gmaj c p.2)

lemma maj_nonneg (c : ℝ) (p : ℤ × ℤ) : 0 ≤ maj c p :=
  mul_nonneg (Real.exp_pos _).le (mul_nonneg (gmaj_nonneg _ _) (gmaj_nonneg _ _))

lemma summable_maj {c : ℝ} (hc : 0 < c) : Summable (maj c) :=
  ((summable_gmaj hc).mul_of_nonneg (summable_gmaj hc) (gmaj_nonneg _) (gmaj_nonneg _)).mul_left _

/-- `Σ_{p ∈ ℤ²} e^c g_c(p.1) g_c(p.2) = 4 e^{-c}/(1 - e^{-c})²`. -/
lemma tsum_maj {c : ℝ} (hc : 0 < c) :
    ∑' p : ℤ × ℤ, maj c p = 4 * (Real.exp (-c) / (1 - Real.exp (-c)) ^ 2) := by
  have hprod := (summable_gmaj hc).mul_of_nonneg (summable_gmaj hc) (gmaj_nonneg _) (gmaj_nonneg _)
  have h1 : 0 < 1 - Real.exp (-c) := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc); linarith
  have hee : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold maj
  rw [tsum_mul_left, ← (summable_gmaj hc).tsum_mul_tsum (summable_gmaj hc) hprod, tsum_gmaj hc]
  field_simp
  linear_combination 4 * hee

variable {u : ℤ → ℤ → ℂ} {A Bk : ℤ → ℝ} {α β : ℝ}

section Bounds

variable (hu : ∀ k y, ‖u k y‖ = 1) (hα : 0 < α) (hβ : 0 < β)
  (hA : ∀ y : ℤ, A y = α * (y : ℝ) ^ 2) (hB : ∀ k : ℤ, Bk k = β * (k : ℝ) ^ 2)
include hu hα hβ hA hB

/-- **Termwise bound (sharp split).** For `re s > 1/2`, with `c = √(αβ)`:
`‖T s (y,k)‖ ≤ Γ(σ - 1/2) (2/α)^{σ - 1/2} · e^c e^{-c|y|} e^{-c|k|}`. -/
theorem norm_T_le {s : ℂ} (hs : 1 / 2 < s.re) (p : ℤ × ℤ) :
    ‖T u A Bk s p‖ ≤ Real.Gamma (s.re - 1 / 2) * (2 / α) ^ (s.re - 1 / 2) * maj (Real.sqrt (α * β)) p := by
  set c := Real.sqrt (α * β) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (mul_pos hα hβ)
  have hΓ : 0 ≤ Real.Gamma (s.re - 1 / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  have h2 : 0 ≤ (2 / α) ^ (s.re - 1 / 2) := Real.rpow_nonneg (by positivity) _
  have hm := maj_nonneg c p
  unfold T
  split_ifs with h
  · rw [norm_zero]; exact mul_nonneg (mul_nonneg hΓ h2) hm
  · obtain ⟨hy, hk⟩ := not_or.mp h
    rw [norm_mul, hu, one_mul]
    have hy1 : (1 : ℝ) ≤ |(p.1 : ℝ)| := by exact_mod_cast Int.one_le_abs hy
    have hk1 : (1 : ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have hy2 : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 := by nlinarith [sq_abs (p.1 : ℝ)]
    have hAy : 0 < A p.1 := by rw [hA]; positivity
    have hBk : 0 ≤ Bk p.2 := by rw [hB]; positivity
    refine (norm_I_le hAy hBk hs).trans ?_
    have hsq : Real.sqrt (A p.1 * Bk p.2) = c * (|(p.1 : ℝ)| * |(p.2 : ℝ)|) := by
      rw [hA, hB, show α * (p.1 : ℝ) ^ 2 * (β * (p.2 : ℝ) ^ 2) =
          (α * β) * (|(p.1 : ℝ)| * |(p.2 : ℝ)|) ^ 2 by rw [mul_pow, sq_abs, sq_abs]; ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have hexp : Real.exp (-Real.sqrt (A p.1 * Bk p.2)) ≤ maj c p := by
      rw [hsq]
      simp only [maj, gmaj, if_neg hy, if_neg hk]
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have key : |(p.1 : ℝ)| + |(p.2 : ℝ)| - 1 ≤ |(p.1 : ℝ)| * |(p.2 : ℝ)| := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hk1)]
      nlinarith [mul_le_mul_of_nonneg_left key hc.le]
    have hpow : (2 / A p.1) ^ (s.re - 1 / 2) ≤ (2 / α) ^ (s.re - 1 / 2) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
      rw [hA]
      exact div_le_div_of_nonneg_left (by norm_num) hα (le_mul_of_one_le_right hα.le hy2)
    calc Real.exp (-Real.sqrt (A p.1 * Bk p.2)) *
          ((2 / A p.1) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2))
        ≤ maj c p * ((2 / α) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2)) :=
          mul_le_mul hexp (mul_le_mul_of_nonneg_right hpow hΓ) (by positivity) hm
      _ = _ := by ring

theorem summable_norm_T {s : ℂ} (hs : 1 / 2 < s.re) : Summable fun p : ℤ × ℤ => ‖T u A Bk s p‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_T_le hu hα hβ hA hB hs)
    ((summable_maj (Real.sqrt_pos.mpr (mul_pos hα hβ))).mul_left _)

theorem summable_T {s : ℂ} (hs : 1 / 2 < s.re) : Summable (T u A Bk s) :=
  (summable_norm_T hu hα hβ hA hB hs).of_norm

/-- `Σ_{ℤ²} T` as an iterated sum `Σ_y Σ_k`. -/
theorem tsum_T_eq_tsum_tsum {s : ℂ} (hs : 1 / 2 < s.re) :
    ∑' p : ℤ × ℤ, T u A Bk s p = ∑' y : ℤ, ∑' k : ℤ, T u A Bk s (y, k) :=
  (summable_T hu hα hβ hA hB hs).tsum_prod' fun y => (summable_T hu hα hβ hA hB hs).prod_factor y

/-- **The sharp bound on the sum:** `‖Σ T s p‖ ≤ Γ(σ - 1/2) (2/α)^{σ - 1/2} · 4e^{-c}/(1 - e^{-c})²`. -/
theorem norm_tsum_T_le {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖∑' p : ℤ × ℤ, T u A Bk s p‖ ≤ Real.Gamma (s.re - 1 / 2) * (2 / α) ^ (s.re - 1 / 2) *
      (4 * (Real.exp (-Real.sqrt (α * β)) / (1 - Real.exp (-Real.sqrt (α * β))) ^ 2)) := by
  have hc : 0 < Real.sqrt (α * β) := Real.sqrt_pos.mpr (mul_pos hα hβ)
  calc ‖∑' p : ℤ × ℤ, T u A Bk s p‖ ≤ ∑' p : ℤ × ℤ, ‖T u A Bk s p‖ :=
        norm_tsum_le_tsum_norm (summable_norm_T hu hα hβ hA hB hs)
    _ ≤ ∑' p : ℤ × ℤ, Real.Gamma (s.re - 1 / 2) * (2 / α) ^ (s.re - 1 / 2) * maj (Real.sqrt (α * β)) p :=
        Summable.tsum_le_tsum (norm_T_le hu hα hβ hA hB hs) (summable_norm_T hu hα hβ hA hB hs)
          ((summable_maj hc).mul_left _)
    _ = _ := by rw [tsum_mul_left, tsum_maj hc]

omit hu in
lemma differentiableOn_T (p : ℤ × ℤ) :
    DifferentiableOn ℂ (fun s => T u A Bk s p) {s : ℂ | 1 / 2 < s.re} := by
  by_cases h : p.1 = 0 ∨ p.2 = 0
  · simp only [T, if_pos h]
    exact differentiableOn_const 0
  · simp only [T, if_neg h]
    have hy0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast (not_or.mp h).1
    have hAy : 0 < A p.1 := by rw [hA]; positivity
    have hBk : 0 ≤ Bk p.2 := by rw [hB]; positivity
    intro s hs
    exact ((differentiableAt_I hAy hBk hs).const_mul _).differentiableWithinAt

/-- **Holomorphy:** `s ↦ Σ_{ℤ²} T s p` is holomorphic on `re s > 1/2` (uniform majorant on strips, with `Γ` bounded
there by convexity, as in CN-1's `differentiableAt_S`). -/
theorem differentiableOn_tsum_T :
    DifferentiableOn ℂ (fun s => ∑' p : ℤ × ℤ, T u A Bk s p) {s : ℂ | 1 / 2 < s.re} := by
  intro s₀ hs₀
  simp only [mem_setOf_eq] at hs₀
  set δ : ℝ := (s₀.re - 1 / 2) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set U : Set ℂ := {s | s₀.re - δ < s.re} ∩ {s | s.re < s₀.re + δ} with hU
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hs₀U : s₀ ∈ U := ⟨by simp only [mem_setOf_eq]; linarith, by simp only [mem_setOf_eq]; linarith⟩
  have hUsub : U ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    obtain ⟨h1, _⟩ := hs
    simp only [mem_setOf_eq] at h1 ⊢
    linarith
  set CΓ : ℝ := max (Real.Gamma δ) (Real.Gamma (3 * δ)) with hCΓ
  have hCΓ0 : 0 ≤ CΓ := le_max_of_le_left (Real.Gamma_pos_of_pos hδpos).le
  have hΓle : ∀ s ∈ U, Real.Gamma (s.re - 1 / 2) ≤ CΓ := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    simp only [mem_setOf_eq] at h1 h2
    apply Real.convexOn_Gamma.le_on_segment (mem_Ioi.mpr hδpos) (mem_Ioi.mpr (by linarith))
    rw [segment_eq_Icc (by linarith)]
    exact ⟨by linarith, by linarith⟩
  set M : ℝ := max 1 (2 / α) ^ (3 * δ) with hM
  have hM0 : 0 ≤ M := Real.rpow_nonneg (le_max_of_le_left zero_le_one) _
  have hMle : ∀ s ∈ U, (2 / α) ^ (s.re - 1 / 2) ≤ M := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    simp only [mem_setOf_eq] at h1 h2
    calc (2 / α) ^ (s.re - 1 / 2) ≤ (max 1 (2 / α)) ^ (s.re - 1 / 2) :=
          Real.rpow_le_rpow (by positivity) (le_max_right _ _) (by linarith)
      _ ≤ M := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by linarith)
  have hc : 0 < Real.sqrt (α * β) := Real.sqrt_pos.mpr (mul_pos hα hβ)
  have hsum := (summable_maj hc).mul_left (CΓ * M)
  have hdiff : DifferentiableOn ℂ (fun w => ∑' p : ℤ × ℤ, T u A Bk w p) U := by
    refine differentiableOn_tsum_of_summable_norm hsum
      (fun p => (differentiableOn_T hα hβ hA hB p).mono hUsub) hUopen (fun p w hw => ?_)
    have hw' : 1 / 2 < w.re := hUsub hw
    refine (norm_T_le hu hα hβ hA hB hw' p).trans ?_
    have h20 : 0 ≤ (2 / α) ^ (w.re - 1 / 2) := Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hΓle w hw) (hMle w hw) h20 hCΓ0) (maj_nonneg _ _)
  exact (hdiff.differentiableAt (hUopen.mem_nhds hs₀U)).differentiableWithinAt

/-- The slice `y ≠ 0` of `Σ_k u(k, y) I(s; A_y, B_k)`, with the `k = 0` term separated. -/
theorem tsum_u_I_split {s : ℂ} (hs : 1 / 2 < s.re) {y : ℤ} (hy : y ≠ 0) :
    ∑' k : ℤ, u k y * I s (A y) (Bk k) = u 0 y * I s (A y) (Bk 0) + ∑' k : ℤ, T u A Bk s (y, k) := by
  have hsum : Summable fun k : ℤ => u k y * I s (A y) (Bk k) := by
    have h1 := (summable_T hu hα hβ hA hB hs).prod_factor y
    have h2 : Summable fun k : ℤ => if k = 0 then u 0 y * I s (A y) (Bk 0) else 0 :=
      (hasSum_ite_eq 0 _).summable
    refine (h1.add h2).congr fun k => ?_
    by_cases hk : k = 0
    · subst hk; simp [T, hy]
    · simp [T, hy, hk]
  rw [hsum.tsum_eq_add_tsum_ite 0]
  congr 1
  exact tsum_congr fun k => by by_cases hk : k = 0 <;> simp [T, hy, hk]

end Bounds

/-- **Reality at real `σ`.** If `conj u(k, y) = u(-k, y)` and `B_{-k} = B_k`, then `Σ_{ℤ²} T σ p` is real
(the reindexing `(y, k) ↦ (y, -k)` conjugates every term, and `I(σ; A, B)` is real). -/
theorem tsum_T_ofReal_im (hu : ∀ k y, (starRingEnd ℂ) (u k y) = u (-k) y) (hB : ∀ k, Bk (-k) = Bk k)
    (σ : ℝ) : (∑' p : ℤ × ℤ, T u A Bk (σ : ℂ) p).im = 0 := by
  have hT : ∀ p : ℤ × ℤ, (starRingEnd ℂ) (T u A Bk σ p) = T u A Bk σ (p.1, -p.2) := by
    intro p
    simp only [T, neg_eq_zero]
    split_ifs
    · simp
    · rw [map_mul, hu, I_ofReal, Complex.conj_ofReal, ← I_ofReal, hB]
  have e : (starRingEnd ℂ) (∑' p : ℤ × ℤ, T u A Bk σ p) = ∑' p : ℤ × ℤ, T u A Bk σ p := by
    rw [Complex.conj_tsum]
    simp_rw [hT]
    exact (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).tsum_eq (fun p => T u A Bk σ p)
  exact Complex.conj_eq_iff_im.mp e

end HCN.CSAux
