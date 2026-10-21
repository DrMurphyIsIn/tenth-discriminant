/- telperion 0.1.6 | family SOSSDP | input-hash a4f4d696c2e006c1
   3 theorems, 12 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace SOSSDP

-- sdp_sos_interior_tie: SDP-SOS certificate (PSD Gram, off-diagonal coupling).
-- Tight variety (0 ≤ p is tight iff): 1 - (1 / 2) * x - (1 / 2) * y = 0 ∧ x - y = 0
theorem sdp_sos_interior_tie : ∀ x y : ℝ, (0:ℝ) ≤ 2 + 2 * x ^ 2 + 2 * y ^ 2 - 2 * x - 2 * y - 2 * x * y := by
  intro x y
  have hsos : (2 + 2 * x ^ 2 + 2 * y ^ 2 - 2 * x - 2 * y - 2 * x * y : ℝ) = 2 * (1 - (1 / 2) * x - (1 / 2) * y)^2 + (3 / 2) * (x - y)^2 := by ring
  rw [hsos]; positivity

-- sdp_sos_interior_tie_a2: SDP-SOS certificate (PSD Gram, off-diagonal coupling).
-- Tight variety (0 ≤ p is tight iff): 1 - (1 / 2) * x = 0 ∧ x - 2 * y = 0
theorem sdp_sos_interior_tie_a2 : ∀ x y : ℝ, (0:ℝ) ≤ 6 + 2 * x ^ 2 + 2 * y ^ 2 - 6 * x - 2 * x * y := by
  intro x y
  have hsos : (6 + 2 * x ^ 2 + 2 * y ^ 2 - 6 * x - 2 * x * y : ℝ) = 6 * (1 - (1 / 2) * x)^2 + (1 / 2) * (x - 2 * y)^2 := by ring
  rw [hsos]; positivity

-- sdp_sos_interior_tie_a3: SDP-SOS certificate (PSD Gram, off-diagonal coupling).
-- Tight variety (0 ≤ p is tight iff): 1 + (1 / 14) * y - (5 / 14) * x = 0 ∧ x - 3 * y = 0
theorem sdp_sos_interior_tie_a3 : ∀ x y : ℝ, (0:ℝ) ≤ 14 + 2 * y + 2 * x ^ 2 + 2 * y ^ 2 - 10 * x - 2 * x * y := by
  intro x y
  have hsos : (14 + 2 * y + 2 * x ^ 2 + 2 * y ^ 2 - 10 * x - 2 * x * y : ℝ) = 14 * (1 + (1 / 14) * y - (5 / 14) * x)^2 + (3 / 14) * (x - 3 * y)^2 := by ring
  rw [hsos]; positivity

end SOSSDP
end G1
