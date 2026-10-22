import CN1.Numerics.GammaBounds
import CN1.Numerics.RpowBounds

/-!
# The enclosure `2.1753 ≤ Γ(3/8)/Γ(7/8) ≤ 2.1755`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

`Gamma_ratio_bounds` (GammaBounds.lean) with `n = 8000`, `x₁ = 3/8`, `x₂ = 7/8`:

  `8000 (8000+3/8)^(-5/8) / 8000^(7/8) · P ≤ Γ(3/8)/Γ(7/8) ≤ 8000^(3/8) / (8000 (8000+7/8)^(-1/8)) · P`,

`P = ∏_{k<8000} (7/8+k)/(3/8+k) = gA / gB` with `gA = ∏ (8k+7)`, `gB = ∏ (8k+3)` (34977-digit naturals,
computed by the kernel in 40 blocks of 200). The four `rpow` factors are bracketed at scale `10^12`
by integer root inequalities, and the two final comparisons are `Nat` inequalities decided by the
kernel (`decide +kernel`, GMP-accelerated).

COMPUTED (certificates/gen_gamma_numbers.py, exact rationals): the enclosure is `[2.175359180, 2.175452652]`;
mpmath gives `Γ(3/8)/Γ(7/8) = 2.17540591572…`. The Lean statement uses `2.1753 ≤ · ≤ 2.1755`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace CN1.Numerics

open Real

/-! ### Brackets for a rational base `a/b` -/

/-- `L^q a^p ≤ b^p S^q` gives `L/S ≤ (a/b)^(-p/q)`. -/
lemma rpow_rat_neg_div_lower (a b p q L S : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hS : 0 < S)
    (hL : L ^ q * a ^ p ≤ b ^ p * S ^ q) : (L : ℝ) / S ≤ ((a : ℝ) / b) ^ (-((p : ℝ) / q)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hab : (0 : ℝ) < (a : ℝ) / b := by positivity
  have hy : (0 : ℝ) ≤ ((a : ℝ) / b) ^ (-((p : ℝ) / q)) := Real.rpow_nonneg hab.le _
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hyq : (((a : ℝ) / b) ^ (-((p : ℝ) / q))) ^ q = (b : ℝ) ^ p / (a : ℝ) ^ p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hab.le, neg_mul, div_mul_cancel₀ _ hq',
      Real.rpow_neg hab.le, Real.rpow_natCast, div_pow, inv_div]
  have hS' : (0 : ℝ) < S := by exact_mod_cast hS
  rw [← pow_le_pow_iff_left₀ (by positivity) hy hq.ne', hyq, div_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hL

/-! ### The exact rational `P = gA / gB` -/

/-- `∏_{k<8000} (8k+7)`, in 40 blocks of 200. Only the kernel ever evaluates it (`key_lo`,
`key_hi`); the real-number argument is made for abstract `A B : ℕ` so that no tactic tries to. -/
def gA : ℕ := ∏ c ∈ Finset.range 40, ∏ j ∈ Finset.range 200, (8 * (200 * c + j) + 7)

/-- `∏_{k<8000} (8k+3)`, in 40 blocks of 200. -/
def gB : ℕ := ∏ c ∈ Finset.range 40, ∏ j ∈ Finset.range 200, (8 * (200 * c + j) + 3)

lemma gA_eq : (∏ k ∈ Finset.range 8000, (8 * k + 7)) = gA := by
  rw [show (8000 : ℕ) = 40 * 200 from rfl, prod_range_chunk]
  rfl

lemma gB_eq : (∏ k ∈ Finset.range 8000, (8 * k + 3)) = gB := by
  rw [show (8000 : ℕ) = 40 * 200 from rfl, prod_range_chunk]
  rfl

lemma P_eq : (∏ k ∈ Finset.range 8000, ((7 : ℝ) / 8 + k) / ((3 : ℝ) / 8 + k)) = (gA : ℝ) / gB := by
  rw [← gA_eq, ← gB_eq, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h3 : (3 : ℝ) / 8 + k ≠ 0 := by positivity
  have h3' : (8 : ℝ) * k + 3 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma gB_pos : 0 < gB := by
  unfold gB
  exact Finset.prod_pos fun c _ => Finset.prod_pos fun j _ => by omega

/-! ### The two kernel comparisons -/

/-- `21753 · u₂ · gB ≤ 10000 · 8000 · l₁ · gA`. -/
lemma key_lo : 21753 * 2601379650496946 * gB ≤ 10000 * 8000 * 3635432077 * gA := by
  decide +kernel

/-- `10000 · u₃ · gA ≤ 21755 · 8000 · l₄ · gB`. -/
lemma key_hi : 10000 * 29084308668980 * gA ≤ 21755 * 8000 * 325168010868 * gB := by
  decide +kernel

/-! ### Brackets for the four `rpow` factors (scale `10^12`) -/

lemma g_hA : (3635432077 : ℝ) / 1000000000000 ≤ ((8000 : ℝ) + 3 / 8) ^ ((3 : ℝ) / 8 - 1) := by
  have := rpow_rat_neg_div_lower 64003 8 5 8 3635432077 1000000000000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma g_hB : (8000 : ℝ) ^ ((7 : ℝ) / 8) ≤ (2601379650496946 : ℝ) / 1000000000000 := by
  have := rpow_div_upper 8000 7 8 2601379650496946 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma g_hC : (8000 : ℝ) ^ ((3 : ℝ) / 8) ≤ (29084308668980 : ℝ) / 1000000000000 := by
  have := rpow_div_upper 8000 3 8 29084308668980 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2
  all_goals norm_num

lemma g_hD : (325168010868 : ℝ) / 1000000000000 ≤ ((8000 : ℝ) + 7 / 8) ^ ((7 : ℝ) / 8 - 1) := by
  have := rpow_rat_neg_div_lower 64007 8 1 8 325168010868 1000000000000 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)
  convert this using 2
  all_goals norm_num

/-! ### The enclosure -/

/-- The real-number argument, for abstract `A B : ℕ` standing for `gA`, `gB` (so that no tactic
tries to evaluate the 35000-digit products). -/
theorem Gamma_ratio_enclosure_aux (gA gB : ℕ) (gB_pos : 0 < gB)
    (P_eq : (∏ k ∈ Finset.range 8000, ((7 : ℝ) / 8 + k) / ((3 : ℝ) / 8 + k)) = (gA : ℝ) / gB)
    (key_lo : 21753 * 2601379650496946 * gB ≤ 10000 * 8000 * 3635432077 * gA)
    (key_hi : 10000 * 29084308668980 * gA ≤ 21755 * 8000 * 325168010868 * gB) :
    (2.1753 : ℝ) ≤ Gamma (3 / 8) / Gamma (7 / 8) ∧ Gamma (3 / 8) / Gamma (7 / 8) ≤ 2.1755 := by
  obtain ⟨hlo, hhi⟩ := Gamma_ratio_bounds 8000 (by norm_num) (x₁ := 3 / 8) (x₂ := 7 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [P_eq] at hlo hhi
  clear P_eq
  push_cast at hlo hhi
  have hgA : (0 : ℝ) ≤ gA := Nat.cast_nonneg gA
  have hgB : (0 : ℝ) < gB := Nat.cast_pos.mpr gB_pos
  have hY : (0 : ℝ) < (8000 : ℝ) ^ ((7 : ℝ) / 8) := by positivity
  have hD' : (0 : ℝ) < ((8000 : ℝ) + 7 / 8) ^ ((7 : ℝ) / 8 - 1) := by positivity
  have hkey1 : (21753 : ℝ) * 2601379650496946 * gB ≤ 10000 * 8000 * 3635432077 * gA := by
    exact_mod_cast key_lo
  have hkey2 : (10000 : ℝ) * 29084308668980 * gA ≤ 21755 * 8000 * 325168010868 * gB := by
    exact_mod_cast key_hi
  clear key_lo key_hi gB_pos
  constructor
  · calc (2.1753 : ℝ)
        ≤ (8000 : ℝ) * ((3635432077 : ℝ) / 1000000000000) / ((2601379650496946 : ℝ) / 1000000000000)
            * ((gA : ℝ) / gB) := by
          rw [show (8000 : ℝ) * ((3635432077 : ℝ) / 1000000000000)
              / ((2601379650496946 : ℝ) / 1000000000000) * ((gA : ℝ) / gB)
              = (8000 * 3635432077 * gA) / (2601379650496946 * gB) by field_simp]
          rw [le_div_iff₀ (by positivity)]
          linarith
      _ ≤ (8000 : ℝ) * ((8000 : ℝ) + 3 / 8) ^ ((3 : ℝ) / 8 - 1) / (8000 : ℝ) ^ ((7 : ℝ) / 8)
            * ((gA : ℝ) / gB) := by
          gcongr
          · exact g_hA
          · exact g_hB
      _ ≤ Gamma (3 / 8) / Gamma (7 / 8) := hlo
  · calc Gamma (3 / 8) / Gamma (7 / 8)
        ≤ (8000 : ℝ) ^ ((3 : ℝ) / 8) / ((8000 : ℝ) * ((8000 : ℝ) + 7 / 8) ^ ((7 : ℝ) / 8 - 1))
            * ((gA : ℝ) / gB) := hhi
      _ ≤ ((29084308668980 : ℝ) / 1000000000000)
            / ((8000 : ℝ) * ((325168010868 : ℝ) / 1000000000000)) * ((gA : ℝ) / gB) := by
          gcongr
          · exact g_hC
          · exact g_hD
      _ ≤ 2.1755 := by
          rw [show ((29084308668980 : ℝ) / 1000000000000)
              / ((8000 : ℝ) * ((325168010868 : ℝ) / 1000000000000)) * ((gA : ℝ) / gB)
              = (29084308668980 * gA) / (8000 * 325168010868 * gB) by field_simp]
          rw [div_le_iff₀ (by positivity)]
          linarith

/-- `2.1753 ≤ Γ(3/8)/Γ(7/8) ≤ 2.1755`, about Mathlib's `Real.Gamma`. -/
theorem Gamma_ratio_enclosure :
    (2.1753 : ℝ) ≤ Gamma (3 / 8) / Gamma (7 / 8) ∧ Gamma (3 / 8) / Gamma (7 / 8) ≤ 2.1755 :=
  Gamma_ratio_enclosure_aux gA gB gB_pos P_eq key_lo key_hi

end CN1.Numerics
