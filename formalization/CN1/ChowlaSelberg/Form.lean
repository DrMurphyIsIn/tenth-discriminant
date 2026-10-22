import Mathlib

/-!
# CN1.ChowlaSelberg.Form: the principal form and the Epstein sum

For a discriminant `d` with `d ≡ 0 or 3 (mod 4)` we set `b = d % 2` (so `b = 1` iff `d ≡ 3`),
`c = (d + b) / 4`, and the principal form `Q(x, y) = x² + b x y + c y²`, so that
`Q(x, y) = (x + b y / 2)² + (d / 4) y²` and `Q(x, y) ≥ (x² + y²) / 2` once `c ≥ 1` (`d ≥ 3`).

The Epstein sum is `Z d s = Σ_{p ∈ ℤ²} Q(p)^{-s}`; the term at `p = 0` is `0 ^ (-s) = 0`
(Mathlib's `cpow`), so this is the primed sum `Σ′`. It converges absolutely for `re s > 1`
(from `EisensteinSeries.summable_one_div_norm_rpow`, following openai/math's
`LatticeSummability.lean` for the form `x² - xy + y²`).
-/

open Complex Set

namespace CN1.CS

/-- `d ≡ 0 or 3 (mod 4)`: the (absolute) discriminant of an imaginary quadratic field. -/
def IsDisc (d : ℕ) : Prop := d % 4 = 0 ∨ d % 4 = 3

/-- `b = d mod 2`, the middle coefficient of the principal form. -/
def bq (d : ℕ) : ℕ := d % 2

/-- `c = (d + b) / 4`, the last coefficient of the principal form. -/
def cq (d : ℕ) : ℕ := (d + d % 2) / 4

/-- The principal form `Q(x, y) = x² + b x y + c y²`, real-valued on `ℤ²`. -/
noncomputable def Q (d : ℕ) (x y : ℤ) : ℝ :=
  (x : ℝ) ^ 2 + (bq d : ℝ) * x * y + (cq d : ℝ) * (y : ℝ) ^ 2

/-- The Epstein zeta sum `Z_Q(s) = Σ′ Q(x, y)^{-s}` (the `p = 0` term vanishes for `s ≠ 0`). -/
noncomputable def Z (d : ℕ) (s : ℂ) : ℂ := ∑' p : ℤ × ℤ, (Q d p.1 p.2 : ℂ) ^ (-s)

variable {d : ℕ}

lemma bq_eq_zero_or_one (d : ℕ) : bq d = 0 ∨ bq d = 1 := Nat.mod_two_eq_zero_or_one d

lemma bq_sq (d : ℕ) : bq d ^ 2 = bq d := by
  rcases bq_eq_zero_or_one d with h | h <;> simp [h]

lemma four_mul_cq (hd : IsDisc d) : 4 * cq d = d + bq d := by
  unfold cq bq; rcases hd with h | h <;> omega

lemma one_le_cq (hd : IsDisc d) (h3 : 3 ≤ d) : 1 ≤ cq d := by
  unfold cq; rcases hd with h | h <;> omega

lemma Q_eq (hd : IsDisc d) (x y : ℤ) :
    Q d x y = ((x : ℝ) + (bq d : ℝ) * y / 2) ^ 2 + (d : ℝ) / 4 * (y : ℝ) ^ 2 := by
  have h1 : (4 * cq d : ℝ) = d + bq d := by exact_mod_cast four_mul_cq hd
  have h2 : (bq d : ℝ) ^ 2 = bq d := by exact_mod_cast bq_sq d
  unfold Q
  linear_combination ((y : ℝ) ^ 2 / 4) * h1 - ((y : ℝ) ^ 2 / 4) * h2

lemma Q_ge_half (hd : IsDisc d) (h3 : 3 ≤ d) (x y : ℤ) :
    (1 / 2 : ℝ) * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) ≤ Q d x y := by
  have hc : (1 : ℝ) ≤ cq d := by exact_mod_cast one_le_cq hd h3
  unfold Q
  rcases bq_eq_zero_or_one d with h | h
  · simp only [h, Nat.cast_zero, zero_mul]
    nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ)]
  · simp only [h, Nat.cast_one, one_mul]
    nlinarith [sq_nonneg ((x : ℝ) + y), sq_nonneg (y : ℝ)]

lemma Q_nonneg (hd : IsDisc d) (h3 : 3 ≤ d) (x y : ℤ) : 0 ≤ Q d x y :=
  le_trans (by positivity) (Q_ge_half hd h3 x y)

lemma Q_pos_of_ne_zero (hd : IsDisc d) (h3 : 3 ≤ d) {x y : ℤ} (hy : y ≠ 0) : 0 < Q d x y := by
  have hy' : (0 : ℝ) < (y : ℝ) ^ 2 := by
    have : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    positivity
  have := Q_ge_half hd h3 x y
  nlinarith [sq_nonneg (x : ℝ)]

lemma Q_ge_quarter_sq (hd : IsDisc d) (x y : ℤ) : (d : ℝ) / 4 * (y : ℝ) ^ 2 ≤ Q d x y := by
  rw [Q_eq hd]; nlinarith [sq_nonneg ((x : ℝ) + (bq d : ℝ) * y / 2)]

/-- `‖p‖² ≤ x² + y²` for `p = (x, y) ∈ ℤ²` with the sup norm. -/
lemma norm_sq_le (p : ℤ × ℤ) : ‖p‖ ^ 2 ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
  rw [Prod.norm_def, ← Int.norm_cast_real, ← Int.norm_cast_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  rcases le_total |(p.1 : ℝ)| |(p.2 : ℝ)| with h | h
  · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg (p.1 : ℝ)]
  · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg (p.2 : ℝ)]

lemma Q_ge_half_norm_sq (hd : IsDisc d) (h3 : 3 ≤ d) (p : ℤ × ℤ) :
    (1 / 2 : ℝ) * ‖p‖ ^ 2 ≤ Q d p.1 p.2 :=
  le_trans (by have := norm_sq_le p; linarith) (Q_ge_half hd h3 p.1 p.2)

lemma Q_pos (hd : IsDisc d) (h3 : 3 ≤ d) {p : ℤ × ℤ} (hp : p ≠ 0) : 0 < Q d p.1 p.2 := by
  have h := Q_ge_half_norm_sq hd h3 p
  have : 0 < ‖p‖ := norm_pos_iff.mpr hp
  nlinarith

/-- `Σ_{p ∈ ℤ²} ‖p‖^{-k}` converges for `k > 2` (sup norm); from openai/math's pattern. -/
theorem summable_pair_norm_rpow {k : ℝ} (hk : 2 < k) :
    Summable (fun n : ℤ × ℤ => ‖n‖ ^ (-k)) := by
  have h := (finTwoArrowEquiv ℤ).symm.summable_iff.mpr
    (EisensteinSeries.summable_one_div_norm_rpow hk)
  have hn (n : ℤ) : (n.natAbs : ℝ) = ‖n‖ := by
    exact congrArg (fun x : NNReal => (x : ℝ)) (NNReal.natCast_natAbs n)
  simpa only [finTwoArrowEquiv_symm_apply, Function.comp_def,
    EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero,
    Matrix.cons_val_one, Prod.norm_def, Nat.cast_max, hn] using h

/-- Absolute convergence of the Epstein sum, real form: `Σ Q(p)^{-σ} < ∞` for `σ > 1`. -/
theorem summable_Q_rpow (hd : IsDisc d) (h3 : 3 ≤ d) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : ℤ × ℤ => Q d p.1 p.2 ^ (-σ)) := by
  have hmajor := (summable_pair_norm_rpow (k := 2 * σ) (by linarith)).mul_left
    ((1 / 2 : ℝ) ^ (-σ))
  apply Summable.of_nonneg_of_le
    (fun p => Real.rpow_nonneg (Q_nonneg hd h3 _ _) _) _ hmajor
  intro p
  by_cases hp : p = 0
  · subst p
    simp [Q, Real.zero_rpow (by linarith : -σ ≠ 0),
      Real.zero_rpow (by linarith : -(2 * σ) ≠ 0)]
  · have hnpos : 0 < ‖p‖ := norm_pos_iff.mpr hp
    calc
      Q d p.1 p.2 ^ (-σ) ≤ ((1 / 2 : ℝ) * ‖p‖ ^ 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (Q_ge_half_norm_sq hd h3 p)
          (by linarith)
      _ = (1 / 2 : ℝ) ^ (-σ) * ‖p‖ ^ (-(2 * σ)) := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg _)]
        congr 1
        rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring

/-- Absolute convergence of the Epstein sum, complex form: `Σ Q(p)^{-s}` for `re s > 1`. -/
theorem summable_Q_cpow (hd : IsDisc d) (h3 : 3 ≤ d) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : ℤ × ℤ => (Q d p.1 p.2 : ℂ) ^ (-s)) := by
  refine Summable.of_norm_bounded (summable_Q_rpow hd h3 hs) fun p => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_nonneg (Q_nonneg hd h3 _ _)
    (by rw [neg_re]; linarith), neg_re]

/-- The slice `x ↦ Q(x, y)^{-s}` is summable for fixed `y` and `re s > 1`. -/
theorem summable_Q_cpow_slice (hd : IsDisc d) (h3 : 3 ≤ d) {s : ℂ} (hs : 1 < s.re) (y : ℤ) :
    Summable (fun x : ℤ => (Q d x y : ℂ) ^ (-s)) :=
  (summable_Q_cpow hd h3 hs).prod_symm.prod_factor y

theorem summable_Q_rpow_slice (hd : IsDisc d) (h3 : 3 ≤ d) {σ : ℝ} (hσ : 1 < σ) (y : ℤ) :
    Summable (fun x : ℤ => Q d x y ^ (-σ)) :=
  (summable_Q_rpow hd h3 hσ).prod_symm.prod_factor y

end CN1.CS
