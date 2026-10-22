import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Rational brackets for `m ^ (±p/q)` and chunked range sums

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

The kernel decides integer inequalities; these lemmas transport them to real `rpow` bounds:

* `rpow_div_lower/upper`: `L^q ≤ m^p S^q` gives `L/S ≤ m^(p/q)`, `m^p S^q ≤ U^q` gives `m^(p/q) ≤ U/S`;
* `rpow_neg_div_lower/upper`: `L^q m^p ≤ S^q` gives `L/S ≤ m^(-p/q)`, `S^q ≤ U^q m^p` gives `m^(-p/q) ≤ U/S`;
* `sum_block_lo_neg/hi_neg`: a block of such brackets, read from a list, bounds a block of a range sum.

`sum_range_chunk` / `prod_range_chunk` split a range sum/product into `C` blocks of `K`, so that
each kernel evaluation stays shallow (ℚ range sums of about 1500 terms exhaust the kernel's recursion
depth; blocks of 300 pass).
-/

set_option autoImplicit false

namespace CN1.Numerics

/-- `L^q ≤ m^p S^q` gives `L/S ≤ m^(p/q)`. -/
lemma rpow_div_lower (m p q L S : ℕ) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q ≤ m ^ p * S ^ q) : (L : ℝ) / S ≤ (m : ℝ) ^ ((p : ℝ) / q) := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ ((p : ℝ) / q) := Real.rpow_nonneg hm _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ ((p : ℝ) / q)) ^ q = (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm, div_mul_cancel₀ _ hq', Real.rpow_natCast]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow, div_le_iff₀ (by positivity)]
  exact_mod_cast hL

/-- `m^p S^q ≤ U^q` gives `m^(p/q) ≤ U/S`. -/
lemma rpow_div_upper (m p q U S : ℕ) (hq : 0 < q) (hS : 0 < S)
    (hU : m ^ p * S ^ q ≤ U ^ q) : (m : ℝ) ^ ((p : ℝ) / q) ≤ (U : ℝ) / S := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ ((p : ℝ) / q) := Real.rpow_nonneg hm _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ ((p : ℝ) / q)) ^ q = (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm, div_mul_cancel₀ _ hq', Real.rpow_natCast]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ hy (by positivity) hq.ne', hyq, div_pow, le_div_iff₀ (by positivity)]
  exact_mod_cast hU

/-- `L^q m^p ≤ S^q` gives `L/S ≤ m^(-p/q)` (for `0 < m`). -/
lemma rpow_neg_div_lower (m p q L S : ℕ) (hm : 0 < m) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q * m ^ p ≤ S ^ q) : (L : ℝ) / S ≤ (m : ℝ) ^ (-((p : ℝ) / q)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hm'.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ (-((p : ℝ) / q))) ^ q = 1 / (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm'.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hm'.le, Real.rpow_natCast, one_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast hL

/-- `S^q ≤ U^q m^p` gives `m^(-p/q) ≤ U/S` (for `0 < m`). -/
lemma rpow_neg_div_upper (m p q U S : ℕ) (hm : 0 < m) (hq : 0 < q) (hS : 0 < S)
    (hU : S ^ q ≤ U ^ q * m ^ p) : (m : ℝ) ^ (-((p : ℝ) / q)) ≤ (U : ℝ) / S := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hy : (0 : ℝ) ≤ (m : ℝ) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hm'.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : ((m : ℝ) ^ (-((p : ℝ) / q))) ^ q = 1 / (m : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm'.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hm'.le, Real.rpow_natCast, one_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ hy (by positivity) hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast hU

/-- A range sum over `C * K` terms as `C` blocks of `K`. -/
lemma sum_range_chunk {M : Type*} [AddCommMonoid M] (f : ℕ → M) (C K : ℕ) :
    ∑ i ∈ Finset.range (C * K), f i
      = ∑ c ∈ Finset.range C, ∑ n ∈ Finset.range K, f (K * c + n) := by
  induction C with
  | zero => simp
  | succ C ih =>
    rw [Finset.sum_range_succ, ← ih, show (C + 1) * K = C * K + K by ring, Finset.sum_range_add,
      mul_comm K C]

/-- A range product over `C * K` terms as `C` blocks of `K`. -/
lemma prod_range_chunk {M : Type*} [CommMonoid M] (f : ℕ → M) (C K : ℕ) :
    ∏ i ∈ Finset.range (C * K), f i
      = ∏ c ∈ Finset.range C, ∏ n ∈ Finset.range K, f (K * c + n) := by
  induction C with
  | zero => simp
  | succ C ih =>
    rw [Finset.prod_range_succ, ← ih, show (C + 1) * K = C * K + K by ring, Finset.prod_range_add,
      mul_comm K C]

/-- Transport of a block of lower brackets to a block of a real range sum (negative exponent
`e = -p/q`). `f` is the summand, `base` the block offset. -/
lemma sum_block_lo_neg (f : ℕ → ℝ) (e : ℝ) (p q S K base : ℕ) (hq : 0 < q) (hS : 0 < S)
    (he : e = -((p : ℝ) / q)) (hf : ∀ i, f i = ((i : ℝ) + 1) ^ e) (lo : List ℕ)
    (h : ∀ n < K, (lo.getD n 0) ^ q * (base + n + 1) ^ p ≤ S ^ q) :
    ((∑ n ∈ Finset.range K, lo.getD n 0 : ℕ) : ℝ) / S ≤ ∑ n ∈ Finset.range K, f (base + n) := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn' : n < K := Finset.mem_range.mp hn
  have := rpow_neg_div_lower (base + n + 1) p q (lo.getD n 0) S (by omega) hq hS (h n hn')
  rw [hf, he]
  convert this using 2
  push_cast
  ring

/-- Transport of a block of upper brackets to a block of a real range sum (negative exponent
`e = -p/q`). -/
lemma sum_block_hi_neg (f : ℕ → ℝ) (e : ℝ) (p q S K base : ℕ) (hq : 0 < q) (hS : 0 < S)
    (he : e = -((p : ℝ) / q)) (hf : ∀ i, f i = ((i : ℝ) + 1) ^ e) (hi : List ℕ)
    (h : ∀ n < K, S ^ q ≤ (hi.getD n 0) ^ q * (base + n + 1) ^ p) :
    ∑ n ∈ Finset.range K, f (base + n) ≤ ((∑ n ∈ Finset.range K, hi.getD n 0 : ℕ) : ℝ) / S := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn' : n < K := Finset.mem_range.mp hn
  have := rpow_neg_div_upper (base + n + 1) p q (hi.getD n 0) S (by omega) hq hS (h n hn')
  rw [hf, he]
  convert this using 2
  push_cast
  ring

end CN1.Numerics
