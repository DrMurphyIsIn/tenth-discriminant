import CN1.ChowlaSelberg.SevenEighths

/-!
# HCN.CS.Form: a positive definite form `a x² + b x y + c y²`

Generic facts about the real quadratic form `q(x, y) = a x² + b x y + c y²` with `a > 0` and `D = 4ac - b² > 0`, stated
over the raw expression (this module declares no interface definition of `HCN.Statements.GeneralCS`):
* `quad_lower`: `D/(4(a+c)) · (x² + y²) ≤ q(x, y)` (the smallest eigenvalue is `(D/4)/λ_max ≥ (D/4)/(a + c)`);
* `quad_eq`: `π q(x, y) = π a (x + by/(2a))² + π D y²/(4a)` (completing the square);
* absolute convergence of `Σ q(p)^{-s}` over `ℤ²` for `re s > 1`, and of its slices.
-/

open Complex Set
open scoped Real

namespace HCN.CSAux

variable {a b c : ℝ}

lemma c_pos (ha : 0 < a) (hD : 0 < 4 * a * c - b ^ 2) : 0 < c := by
  by_contra h
  have h' := not_lt.mp h
  nlinarith [sq_nonneg b]

/-- The lower bound `D/(4(a+c)) · (x² + y²) ≤ a x² + b x y + c y²`. -/
lemma quad_lower (ha : 0 < a) (hD : 0 < 4 * a * c - b ^ 2) (x y : ℝ) :
    (4 * a * c - b ^ 2) / (4 * (a + c)) * (x ^ 2 + y ^ 2) ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  have hc := c_pos ha hD
  set m := (4 * a * c - b ^ 2) / (4 * (a + c)) with hm
  have hm4 : m * (4 * (a + c)) = 4 * a * c - b ^ 2 := by
    rw [hm]; field_simp
  have hma : m < a := by
    have : m * (4 * (a + c)) < a * (4 * (a + c)) := by nlinarith [sq_nonneg b]
    exact lt_of_mul_lt_mul_right this (by positivity)
  have key : (a - m) * (a * x ^ 2 + b * x * y + c * y ^ 2 - m * (x ^ 2 + y ^ 2)) =
      ((a - m) * x + b * y / 2) ^ 2 + m ^ 2 * y ^ 2 := by
    linear_combination (-(y ^ 2) / 4) * hm4
  have h0 : 0 ≤ (a - m) * (a * x ^ 2 + b * x * y + c * y ^ 2 - m * (x ^ 2 + y ^ 2)) := by
    rw [key]; positivity
  by_contra hneg
  have hneg := not_le.mp hneg
  have := mul_neg_of_pos_of_neg (sub_pos.mpr hma) (by linarith :
    a * x ^ 2 + b * x * y + c * y ^ 2 - m * (x ^ 2 + y ^ 2) < 0)
  linarith

lemma kappa_pos (ha : 0 < a) (hD : 0 < 4 * a * c - b ^ 2) : 0 < (4 * a * c - b ^ 2) / (4 * (a + c)) := by
  have hc := c_pos ha hD
  positivity

/-- Completing the square: `π q(x, y) = π a (x + by/(2a))² + π D y²/(4a)`. -/
lemma quad_eq (ha : 0 < a) (x y : ℝ) :
    π * (a * x ^ 2 + b * x * y + c * y ^ 2) =
      π * a * (x + b * y / (2 * a)) ^ 2 + π * (4 * a * c - b ^ 2) * y ^ 2 / (4 * a) := by
  field_simp
  ring

lemma quad_nonneg (ha : 0 < a) (hD : 0 < 4 * a * c - b ^ 2) (x y : ℝ) :
    0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 :=
  le_trans (by have := kappa_pos ha hD; positivity) (quad_lower ha hD x y)

lemma quad_pos_of_ne (ha : 0 < a) (hD : 0 < 4 * a * c - b ^ 2) {x y : ℝ} (hy : y ≠ 0) :
    0 < a * x ^ 2 + b * x * y + c * y ^ 2 := by
  have hk := kappa_pos ha hD
  have hy2 : 0 < y ^ 2 := by positivity
  have := quad_lower ha hD x y
  nlinarith [sq_nonneg x]

/-- Absolute convergence, real form: `Σ_{p ∈ ℤ²} q(p)^{-σ} < ∞` for `σ > 1`. -/
theorem summable_quad_rpow (ha : 0 < a) (hD : 0 < 4 * a * c - b ^ 2) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : ℤ × ℤ => (a * (p.1 : ℝ) ^ 2 + b * p.1 * p.2 + c * (p.2 : ℝ) ^ 2) ^ (-σ)) := by
  set κ := (4 * a * c - b ^ 2) / (4 * (a + c)) with hκ
  have hκ0 : 0 < κ := kappa_pos ha hD
  have hmajor := (CN1.CS.summable_pair_norm_rpow (k := 2 * σ) (by linarith)).mul_left (κ ^ (-σ))
  apply Summable.of_nonneg_of_le
    (fun p => Real.rpow_nonneg (quad_nonneg ha hD _ _) _) _ hmajor
  intro p
  by_cases hp : p = 0
  · subst p
    simp [Real.zero_rpow (by linarith : -σ ≠ 0), Real.zero_rpow (by linarith : -(2 * σ) ≠ 0)]
  · have hnpos : 0 < ‖p‖ := norm_pos_iff.mpr hp
    have hlow : κ * ‖p‖ ^ 2 ≤ a * (p.1 : ℝ) ^ 2 + b * p.1 * p.2 + c * (p.2 : ℝ) ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_left (CN1.CS.norm_sq_le p) hκ0.le) (quad_lower ha hD _ _)
    calc (a * (p.1 : ℝ) ^ 2 + b * p.1 * p.2 + c * (p.2 : ℝ) ^ 2) ^ (-σ)
        ≤ (κ * ‖p‖ ^ 2) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
      _ = κ ^ (-σ) * ‖p‖ ^ (-(2 * σ)) := by
        rw [Real.mul_rpow hκ0.le (sq_nonneg _)]
        congr 1
        rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring

/-- Absolute convergence, complex form: `Σ_{p ∈ ℤ²} q(p)^{-s}` for `re s > 1`. -/
theorem summable_quad_cpow (ha : 0 < a) (hD : 0 < 4 * a * c - b ^ 2) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : ℤ × ℤ =>
      ((a * (p.1 : ℝ) ^ 2 + b * p.1 * p.2 + c * (p.2 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s)) := by
  refine Summable.of_norm_bounded (summable_quad_rpow ha hD hs) fun p => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_nonneg (quad_nonneg ha hD _ _) (by rw [neg_re]; linarith), neg_re]

theorem summable_quad_rpow_slice (ha : 0 < a) (hD : 0 < 4 * a * c - b ^ 2) {σ : ℝ} (hσ : 1 < σ) (y : ℤ) :
    Summable (fun x : ℤ => (a * (x : ℝ) ^ 2 + b * x * y + c * (y : ℝ) ^ 2) ^ (-σ)) :=
  (summable_quad_rpow ha hD hσ).prod_symm.prod_factor y

theorem summable_quad_cpow_slice (ha : 0 < a) (hD : 0 < 4 * a * c - b ^ 2) {s : ℂ} (hs : 1 < s.re) (y : ℤ) :
    Summable (fun x : ℤ => ((a * (x : ℝ) ^ 2 + b * x * y + c * (y : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s)) :=
  (summable_quad_cpow ha hD hs).prod_symm.prod_factor y

end HCN.CSAux
