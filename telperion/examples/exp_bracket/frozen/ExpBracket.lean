/- telperion 0.1.6 | family ExpBracket | input-hash 8d58acf983f0eff7
   6 theorems, 9 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace ExpBracket

theorem exp_neg_theta_far_le :
    Real.exp (-(37167 / 100000 : ℝ)) ≤ 68959 / 100000 := by
  rw [Real.exp_neg, ← one_div]
  have hlow : (29003 / 20000 : ℝ) ≤ Real.exp (37167 / 100000) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 9)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpos : (0 : ℝ) < 29003 / 20000 := by norm_num
  calc 1 / Real.exp (37167 / 100000)
      ≤ 1 / (29003 / 20000 : ℝ) := one_div_le_one_div_of_le hpos hlow
    _ ≤ 68959 / 100000 := by norm_num

theorem exp_neg_theta_far_ge :
    (1 - 37167 / 100000 : ℝ) ≤ Real.exp (-(37167 / 100000)) := by
  have h := Real.add_one_le_exp (-(37167 / 100000 : ℝ))
  linarith

theorem exp_neg_quarter_le :
    Real.exp (-(1 / 4 : ℝ)) ≤ 7789 / 10000 := by
  rw [Real.exp_neg, ← one_div]
  have hlow : (321 / 250 : ℝ) ≤ Real.exp (1 / 4) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 7)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpos : (0 : ℝ) < 321 / 250 := by norm_num
  calc 1 / Real.exp (1 / 4)
      ≤ 1 / (321 / 250 : ℝ) := one_div_le_one_div_of_le hpos hlow
    _ ≤ 7789 / 10000 := by norm_num

theorem exp_neg_quarter_ge :
    (1 - 1 / 4 : ℝ) ≤ Real.exp (-(1 / 4)) := by
  have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
  linarith

theorem exp_neg_half_le :
    Real.exp (-(1 / 2 : ℝ)) ≤ 30327 / 50000 := by
  rw [Real.exp_neg, ← one_div]
  have hlow : (16487 / 10000 : ℝ) ≤ Real.exp (1 / 2) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 9)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpos : (0 : ℝ) < 16487 / 10000 := by norm_num
  calc 1 / Real.exp (1 / 2)
      ≤ 1 / (16487 / 10000 : ℝ) := one_div_le_one_div_of_le hpos hlow
    _ ≤ 30327 / 50000 := by norm_num

theorem exp_neg_half_ge :
    (1 - 1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
  have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
  linarith

end ExpBracket
end G1
