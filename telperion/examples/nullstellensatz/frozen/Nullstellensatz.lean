/- telperion 0.1.6 | family Nullstellensatz | input-hash 662c716728d10190
   2 theorems, 4 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace Nullstellensatz

-- nss_x3_minus_y3: Nullstellensatz certificate  p = Σ h_i·g_i (ideal membership) — p vanishes on the variety.
theorem nss_x3_minus_y3 : ∀ x y : ℝ, x - y = 0 → x ^ 3 - y ^ 3 = 0 := by
  intro x y hg1
  linear_combination (x ^ 2 + x * y + y ^ 2) * hg1

-- nss_xy_in_xy: Nullstellensatz certificate  p = Σ h_i·g_i (ideal membership) — p vanishes on the variety.
theorem nss_xy_in_xy : ∀ x y : ℝ, x = 0 → y = 0 → x * y = 0 := by
  intro x y hg1 hg2
  linear_combination (y) * hg1 + (0) * hg2

end Nullstellensatz
end G1
