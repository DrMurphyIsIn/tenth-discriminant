/- telperion 0.1.6 | family Bernstein | input-hash 41b88eb42e14176e
   3 theorems, 8 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Bernstein

-- bernstein_1_minus_x2: Bernstein-basis positivity (degree 2) — nonnegative Bernstein coefficients on [-1, 1].
theorem bernstein_1_minus_x2 : ∀ x : ℝ, (-1) ≤ x → x ≤ 1 → (0:ℝ) ≤ 1 - x ^ 2 := by
  intro x hlo hhi
  have hxa : (0:ℝ) ≤ 1 + x := by linarith
  have hbx : (0:ℝ) ≤ 1 - x := by linarith
  have t1 : (0:ℝ) ≤ 1 * (1 + x)^1 * (1 - x)^1 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg hxa 1)) (pow_nonneg hbx 1)
  have hid : (1 - x ^ 2 : ℝ) = 1 * (1 + x)^1 * (1 - x)^1 := by ring
  rw [hid]; linarith

-- bernstein_2_minus_x: Bernstein-basis positivity (degree 1) — nonnegative Bernstein coefficients on [0, 1].
theorem bernstein_2_minus_x : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (0:ℝ) ≤ 2 - x := by
  intro x hlo hhi
  have hxa : (0:ℝ) ≤ x := by linarith
  have hbx : (0:ℝ) ≤ 1 - x := by linarith
  have t0 : (0:ℝ) ≤ 2 * (1 - x)^1 := mul_nonneg ((by norm_num : (0:ℝ) ≤ 2)) (pow_nonneg hbx 1)
  have t1 : (0:ℝ) ≤ 1 * (x)^1 := mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg hxa 1)
  have hid : (2 - x : ℝ) = 2 * (1 - x)^1 + 1 * (x)^1 := by ring
  rw [hid]; linarith

-- bernstein_x2_minus_x_plus_1: Bernstein-basis positivity (degree 2) — nonnegative Bernstein coefficients on [0, 1].
theorem bernstein_x2_minus_x_plus_1 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (0:ℝ) ≤ 1 + x ^ 2 - x := by
  intro x hlo hhi
  have hxa : (0:ℝ) ≤ x := by linarith
  have hbx : (0:ℝ) ≤ 1 - x := by linarith
  have t0 : (0:ℝ) ≤ 1 * (1 - x)^2 := mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg hbx 2)
  have t1 : (0:ℝ) ≤ 1 * (x)^1 * (1 - x)^1 := mul_nonneg (mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg hxa 1)) (pow_nonneg hbx 1)
  have t2 : (0:ℝ) ≤ 1 * (x)^2 := mul_nonneg ((by norm_num : (0:ℝ) ≤ 1)) (pow_nonneg hxa 2)
  have hid : (1 + x ^ 2 - x : ℝ) = 1 * (1 - x)^2 + 1 * (x)^1 * (1 - x)^1 + 1 * (x)^2 := by ring
  rw [hid]; linarith

end Bernstein
end G1
