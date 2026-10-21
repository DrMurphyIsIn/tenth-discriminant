/- telperion 0.1.6 | family Cone | input-hash bf84342189b5fa19
   3 theorems, 9 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Cone

theorem cone_square_direct : ∀ x y : ℝ, (0:ℝ) ≤ x ^ 2 + 2 * x * y + y ^ 2 := by
  intro x y
  have hid : x ^ 2 + 2 * x * y + y ^ 2 = 1 * ((x + y) ^ 2) := by ring
  rw [hid]; positivity
theorem cone_square_overcomplete : ∀ x y : ℝ, (0:ℝ) ≤ x ^ 2 + 2 * x * y + y ^ 2 := by
  intro x y
  have hid : x ^ 2 + 2 * x * y + y ^ 2 = 1 * ((x + y) ^ 2) := by ring
  rw [hid]; positivity
theorem cone_sum_of_squares : ∀ x y : ℝ, (0:ℝ) ≤ x ^ 2 + y ^ 2 := by
  intro x y
  have hid : x ^ 2 + y ^ 2 = 1 * (x ^ 2) + 1 * (y ^ 2) := by ring
  rw [hid]; positivity

end Cone
end G1
