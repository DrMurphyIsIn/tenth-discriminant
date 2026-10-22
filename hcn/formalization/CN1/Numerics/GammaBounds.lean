import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Bohr–Mollerup brackets for `Real.Gamma` at rational points

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

Mathlib has `Real.convexOn_log_Gamma` (log-convexity of `Γ` on `(0, ∞)`) and the Bohr–Mollerup
inequalities `Real.BohrMollerup.f_add_nat_le`. From these, for `n ≥ 1` and `0 < x < 1`:

* `Gamma_add_le`:  `Γ(n + x) ≤ Γ(n) n^x`                     (two-point convexity at `n`, `n+1`);
* `Gamma_add_ge`:  `Γ(n+1) (n+x)^(x-1) ≤ Γ(n + x)`            (three-point convexity at `n+x`, `n+1+x`);
* `Gamma_add_nat_eq`: `Γ(n + x) = Γ(x) ∏_{k<n} (x + k)`;
* `Gamma_ratio_bounds`: for `0 < x₁, x₂ < 1`,
  `n (n+x₁)^(x₁-1) / n^x₂ · P ≤ Γ(x₁)/Γ(x₂) ≤ n^x₁ / (n (n+x₂)^(x₂-1)) · P`,
  `P = ∏_{k<n} (x₂+k)/(x₁+k)`; the two sides differ by the factor `(1+x₁/n)^(1-x₁) (1+x₂/n)^(1-x₂)`.

The numerical instance `n = 8000`, `x₁ = 3/8`, `x₂ = 7/8` is in GammaRatio.lean; `P` is an exact
rational the kernel computes.
-/

set_option autoImplicit false

namespace CN1.Numerics

open Real

/-- `Γ(n + x) = Γ(x) ∏_{k<n} (x + k)` for `x > 0`. -/
lemma Gamma_add_nat_eq {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Gamma ((n : ℝ) + x) = Gamma x * ∏ k ∈ Finset.range n, (x + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih, Nat.cast_succ,
      show (n : ℝ) + 1 + x = ((n : ℝ) + x) + 1 by ring, Gamma_add_one (by positivity)]
    ring

lemma log_Gamma_add_one {y : ℝ} (hy : 0 < y) :
    log (Gamma (y + 1)) = log (Gamma y) + log y := by
  rw [Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne', add_comm]

/-- Upper bound: `Γ(n + x) ≤ Γ(n) n^x` for `n ≠ 0`, `0 < x ≤ 1`. -/
lemma Gamma_add_le (n : ℕ) (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Gamma ((n : ℝ) + x) ≤ Gamma n * (n : ℝ) ^ x := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h := Real.BohrMollerup.f_add_nat_le (f := log ∘ Gamma) convexOn_log_Gamma
    (fun {y} hy => log_Gamma_add_one hy) hn hx hx1
  simp only [Function.comp_apply] at h
  have hG : 0 < Gamma ((n : ℝ) + x) := Gamma_pos_of_pos (by positivity)
  have hGn : 0 < Gamma n := Gamma_pos_of_pos hn'
  rw [← exp_log hG, ← exp_log (by positivity : 0 < Gamma n * (n : ℝ) ^ x)]
  apply exp_le_exp.mpr
  rw [log_mul hGn.ne' (rpow_pos_of_pos hn' x).ne', log_rpow hn']
  linarith

/-- Lower bound: `Γ(n+1) (n + x)^(x - 1) ≤ Γ(n + x)` for `0 < x < 1`. -/
lemma Gamma_add_ge (n : ℕ) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Gamma ((n : ℝ) + 1) * ((n : ℝ) + x) ^ (x - 1) ≤ Gamma ((n : ℝ) + x) := by
  have hnx : (0 : ℝ) < n + x := by positivity
  have hnx1 : (0 : ℝ) < n + 1 + x := by positivity
  have hc := convexOn_log_Gamma.2 (Set.mem_Ioi.mpr hnx) (Set.mem_Ioi.mpr hnx1) hx.le
    (by linarith : 0 ≤ 1 - x) (by ring : x + (1 - x) = 1)
  simp only [Function.comp_apply, smul_eq_mul] at hc
  rw [show x * ((n : ℝ) + x) + (1 - x) * ((n : ℝ) + 1 + x) = n + 1 by ring] at hc
  have h2 : log (Gamma ((n : ℝ) + 1 + x)) = log (Gamma (n + x)) + log (n + x) := by
    rw [show (n : ℝ) + 1 + x = (n + x) + 1 by ring]
    exact log_Gamma_add_one hnx
  rw [h2] at hc
  have hG := Gamma_pos_of_pos hnx
  have hG1 : 0 < Gamma ((n : ℝ) + 1) := Gamma_pos_of_pos (by positivity)
  rw [← exp_log hG, ← exp_log (by positivity : 0 < Gamma ((n : ℝ) + 1) * ((n : ℝ) + x) ^ (x - 1))]
  apply exp_le_exp.mpr
  rw [log_mul hG1.ne' (rpow_pos_of_pos hnx _).ne', log_rpow hnx]
  linarith

/-- The ratio `Γ(x₁)/Γ(x₂)` enclosed by elementary functions of `n` times the exact rational
`P = ∏_{k<n} (x₂+k)/(x₁+k)`. -/
theorem Gamma_ratio_bounds (n : ℕ) (hn : n ≠ 0) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₁' : x₁ < 1)
    (hx₂ : 0 < x₂) (hx₂' : x₂ < 1) :
    (n : ℝ) * ((n : ℝ) + x₁) ^ (x₁ - 1) / (n : ℝ) ^ x₂ * (∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k))
        ≤ Gamma x₁ / Gamma x₂ ∧
    Gamma x₁ / Gamma x₂ ≤ (n : ℝ) ^ x₁ / ((n : ℝ) * ((n : ℝ) + x₂) ^ (x₂ - 1))
        * (∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hP1 : 0 < ∏ k ∈ Finset.range n, (x₁ + k) := Finset.prod_pos fun k _ => by positivity
  have hP2 : 0 < ∏ k ∈ Finset.range n, (x₂ + k) := Finset.prod_pos fun k _ => by positivity
  have hP : 0 < ∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k) := Finset.prod_pos fun k _ => by positivity
  have hG2 := Gamma_pos_of_pos hx₂
  have hGn := Gamma_pos_of_pos hn'
  have hGn1 : 0 < Gamma ((n : ℝ) + x₁) := Gamma_pos_of_pos (by positivity)
  have hGn2 : 0 < Gamma ((n : ℝ) + x₂) := Gamma_pos_of_pos (by positivity)
  have e1 := Gamma_add_nat_eq hx₁ n
  have e2 := Gamma_add_nat_eq hx₂ n
  have hratio : Gamma x₁ / Gamma x₂
      = Gamma ((n : ℝ) + x₁) / Gamma ((n : ℝ) + x₂) * ∏ k ∈ Finset.range n, (x₂ + k) / (x₁ + k) := by
    rw [Finset.prod_div_distrib, e1, e2]
    field_simp
    try ring
  have hA := Gamma_add_ge n hx₁ hx₁'
  rw [Gamma_add_one hn'.ne'] at hA
  have hB := Gamma_add_le n hn hx₂ hx₂'.le
  have hC := Gamma_add_le n hn hx₁ hx₁'.le
  have hD := Gamma_add_ge n hx₂ hx₂'
  rw [Gamma_add_one hn'.ne'] at hD
  rw [hratio]
  constructor
  · apply mul_le_mul_of_nonneg_right _ hP.le
    rw [div_le_div_iff₀ (by positivity) hGn2]
    calc (n : ℝ) * ((n : ℝ) + x₁) ^ (x₁ - 1) * Gamma ((n : ℝ) + x₂)
        ≤ (n : ℝ) * ((n : ℝ) + x₁) ^ (x₁ - 1) * (Gamma n * (n : ℝ) ^ x₂) := by gcongr
      _ = ((n : ℝ) * Gamma n * ((n : ℝ) + x₁) ^ (x₁ - 1)) * (n : ℝ) ^ x₂ := by ring
      _ ≤ Gamma ((n : ℝ) + x₁) * (n : ℝ) ^ x₂ := by gcongr
  · apply mul_le_mul_of_nonneg_right _ hP.le
    rw [div_le_div_iff₀ hGn2 (by positivity)]
    calc Gamma ((n : ℝ) + x₁) * ((n : ℝ) * ((n : ℝ) + x₂) ^ (x₂ - 1))
        ≤ (Gamma n * (n : ℝ) ^ x₁) * ((n : ℝ) * ((n : ℝ) + x₂) ^ (x₂ - 1)) := by gcongr
      _ = (n : ℝ) ^ x₁ * ((n : ℝ) * Gamma n * ((n : ℝ) + x₂) ^ (x₂ - 1)) := by ring
      _ ≤ (n : ℝ) ^ x₁ * Gamma ((n : ℝ) + x₂) := by gcongr

end CN1.Numerics
