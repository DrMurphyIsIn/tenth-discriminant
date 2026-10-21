/- telperion 0.1.6 | family Infeasible | input-hash bc6766ab3e55271f
   2 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Infeasible

-- infeasible_x_and_x_minus_1: infeasibility (Nullstellensatz refutation) — the system {g_j = 0} has NO common solution (1 = Σ λ_j g_j).
theorem infeasible_x_and_x_minus_1 : ∀ x y : ℝ, x = 0 → x - 1 = 0 → False := by
  intro x y e1 e2
  have contra : (1:ℝ) = 0 := by linear_combination (1) * e1 + (0 - 1) * e2
  exact absurd contra (by norm_num)

-- infeasible_x2m1_and_x_minus_2: infeasibility (Nullstellensatz refutation) — the system {g_j = 0} has NO common solution (1 = Σ λ_j g_j).
theorem infeasible_x2m1_and_x_minus_2 : ∀ x y : ℝ, x ^ 2 - 1 = 0 → x - 2 = 0 → False := by
  intro x y e1 e2
  have contra : (1:ℝ) = 0 := by linear_combination ((1) / (3)) * e1 + ((0 - 2 - x) / (3)) * e2
  exact absurd contra (by norm_num)

end Infeasible
end G1
