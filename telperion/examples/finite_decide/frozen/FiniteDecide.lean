/- telperion 0.1.6 | family FiniteDecide | input-hash ecb3fc4e6c4d2f09
   1 theorems, 184 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace FiniteDecide

/-- Fueled popcount: structural in fuel, hence kernel-reducible. -/
def pop : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n = 0 then 0 else n % 2 + pop f (n / 2)

def finite_decide_xor3_pairfact_lam : List (ℕ × ℤ) := [(0, 1), (28, 1)]
def finite_decide_xor3_pairfact_lam_get (x : ℕ) : ℤ :=
  (((finite_decide_xor3_pairfact_lam.find? (fun p => p.1 == x)).map Prod.snd).getD 0)

def finite_decide_xor3_pairfact_lamKeys : List ℕ := [0, 28]

def finite_decide_xor3_pairfact_idx : List ℕ := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36, 40, 48]

-- finite_decide_xor3_pairfact: finite decidable certificate (exact-evaluated pre-emission; kernel decide is the final gate).
set_option maxRecDepth 100000 in
theorem finite_decide_xor3_pairfact : ∀ a ∈ finite_decide_xor3_pairfact_lamKeys, ∀ b ∈ finite_decide_xor3_pairfact_lamKeys, ∀ t ∈ finite_decide_xor3_pairfact_idx, pop 16 (a ^^^ t) ≤ 2 → pop 16 (b ^^^ t) ≤ 2 → finite_decide_xor3_pairfact_lam_get (a ^^^ b) = (finite_decide_xor3_pairfact_lam_get a * finite_decide_xor3_pairfact_lam_get b) := by decide

end FiniteDecide
end G1
