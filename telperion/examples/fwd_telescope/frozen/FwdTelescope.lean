/- telperion 0.1.6 | family FwdTelescope | input-hash 35549f8fbd066214
   4 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace FwdTelescope

-- knapsack_fwd_telescope: forward-difference closed form for the recurrence
-- f(q+1) = f(q) * ((n - 2 * q) / (2)) / (n - q); certificate = the contiguous
-- identity A(q) - (P - q - j) + N(j) = 0, verified exactly at certification.

def knapsack_fwd_telescope_f (n : ℚ) : ℕ → ℚ
  | 0 => 1
  | q + 1 => knapsack_fwd_telescope_f n q * ((n - 2 * q) / (2)) / (n - q)

def knapsack_fwd_telescope_pnum (n : ℚ) : ℕ → ℚ
  | 0 => 1
  | u + 1 => knapsack_fwd_telescope_pnum n u * ((n - 2 * u) / (2))

def knapsack_fwd_telescope_pden (n : ℚ) (q : ℕ) : ℕ → ℚ
  | 0 => 1
  | j + 1 => knapsack_fwd_telescope_pden n q j * (n - q - j)

theorem knapsack_fwd_telescope_pden_pos (n : ℚ) (q j : ℕ) (h : (q : ℚ) + j < n + 1) :
    0 < knapsack_fwd_telescope_pden n q j := by
  induction j with
  | zero => norm_num [knapsack_fwd_telescope_pden]
  | succ j ih =>
    have h' : (q : ℚ) + j < n + 1 := by push_cast at h ⊢; linarith
    have hf : (0 : ℚ) < n - q - j := by push_cast at h; linarith
    rw [knapsack_fwd_telescope_pden]
    exact mul_pos (ih h') hf

theorem knapsack_fwd_telescope_pden_shift (n : ℚ) (q j : ℕ) :
    knapsack_fwd_telescope_pden n q (j + 1) = (n - q) * knapsack_fwd_telescope_pden n (q + 1) j := by
  induction j with
  | zero => norm_num [knapsack_fwd_telescope_pden]
  | succ j ih =>
    conv_lhs => rw [knapsack_fwd_telescope_pden]
    rw [ih]
    conv_rhs => rw [knapsack_fwd_telescope_pden]
    push_cast
    ring

/-- The W2 payoff: closed form for the iterated forward difference. -/
theorem knapsack_fwd_telescope_fwdDiff_iter (n : ℚ) (j : ℕ) :
    ∀ q : ℕ, (q : ℚ) + j < n →
      (fwdDiff 1)^[j] (knapsack_fwd_telescope_f n) q
        = (-1) ^ j * knapsack_fwd_telescope_pnum n j * knapsack_fwd_telescope_f n q / knapsack_fwd_telescope_pden n q j := by
  induction j with
  | zero =>
    intro q _
    norm_num [knapsack_fwd_telescope_pnum, knapsack_fwd_telescope_pden]
  | succ j ih =>
    intro q hq
    have hq1 : ((q + 1 : ℕ) : ℚ) + j < n := by push_cast at hq ⊢; linarith
    have hq0 : (q : ℚ) + j < n := by push_cast at hq ⊢; linarith
    have hnq : (0 : ℚ) < n - q := by
      have : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
      push_cast at hq; linarith
    have hnqj : (0 : ℚ) < n - q - j := by push_cast at hq; linarith
    have hB : (0 : ℚ) < knapsack_fwd_telescope_pden n q j :=
      knapsack_fwd_telescope_pden_pos n q j (by push_cast at hq ⊢; linarith)
    have hA : (0 : ℚ) < knapsack_fwd_telescope_pden n (q + 1) j :=
      knapsack_fwd_telescope_pden_pos n (q + 1) j (by push_cast at hq ⊢; linarith)
    have hd : knapsack_fwd_telescope_pden n q (j + 1) = knapsack_fwd_telescope_pden n q j * (n - q - j) := by
      rw [knapsack_fwd_telescope_pden]
    have hArel : knapsack_fwd_telescope_pden n (q + 1) j
        = knapsack_fwd_telescope_pden n q j * (n - q - j) / (n - q) := by
      rw [eq_div_iff (ne_of_gt hnq)]
      linear_combination hd - knapsack_fwd_telescope_pden_shift n q j
    rw [Function.iterate_succ_apply']
    have hstep : fwdDiff 1 ((fwdDiff 1)^[j] (knapsack_fwd_telescope_f n)) q
        = (fwdDiff 1)^[j] (knapsack_fwd_telescope_f n) (q + 1)
          - (fwdDiff 1)^[j] (knapsack_fwd_telescope_f n) q := rfl
    rw [hstep, ih (q + 1) hq1, ih q hq0]
    have hf1 : knapsack_fwd_telescope_f n (q + 1)
        = knapsack_fwd_telescope_f n q * ((n - 2 * q) / (2)) / (n - q) := by rw [knapsack_fwd_telescope_f]
    have hpn : knapsack_fwd_telescope_pnum n (j + 1) = knapsack_fwd_telescope_pnum n j * ((n - 2 * j) / (2)) := by
      rw [knapsack_fwd_telescope_pnum]
    rw [hf1, hpn, hd, hArel, pow_succ]
    field_simp
    ring

end FwdTelescope
end G1
