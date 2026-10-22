import CN1.Numerics.ZetaReal
import CN1.Numerics.ZetaTables

/-!
# Enclosures of `riemannZeta` at `7/4`, `3/4`, `7/8`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

Each value is Mathlib's `riemannZeta` at a complex rational point. The proof is
`riemannZeta_ofReal_eulerMaclaurin` (ZetaReal.lean) with `M = 1000` terms, the kernel-checked
bracket tables of ZetaTables.lean for the finite sum, and single brackets for the three powers of
`N = 1001`. The decimal enclosures are then linear arithmetic.

COMPUTED (certificates/gen_zeta_tables.py, exact rationals; the proofs below do not depend on these
decimals):
  ζ(3/4) ∈ [-3.4412857885, -3.4412842417],  ζ(7/8) ∈ [-7.4319615502, -7.4319607061],
  ζ(7/4) ∈ [ 1.9623200483,  1.9623201526].
Arb (`computations/arb_threshold.py` in this repository): ζ(3/4) = -3.44128…, ζ(7/8) = -7.43196…,
ζ(7/4) = 1.96232….
-/

set_option autoImplicit false

namespace CN1.Numerics

open Real

/-! ### Single brackets for `N = 1001` -/

lemma n1001_quarter_lo : (5624818578328 : ℝ) / 1000000000000 ≤ (((1000 : ℕ) : ℝ) + 1) ^ (1 - (3 : ℝ) / 4) := by
  have := rpow_div_lower 1001 1 4 5624818578328 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_quarter_hi : (((1000 : ℕ) : ℝ) + 1) ^ (1 - (3 : ℝ) / 4) ≤ (5624818578329 : ℝ) / 1000000000000 := by
  have := rpow_div_upper 1001 1 4 5624818578329 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_neg34_lo : (5619199378 : ℝ) / 1000000000000 ≤ (((1000 : ℕ) : ℝ) + 1) ^ (-((3 : ℝ) / 4)) := by
  have := rpow_neg_div_lower 1001 3 4 5619199378 1000000000000 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_neg34_hi : (((1000 : ℕ) : ℝ) + 1) ^ (-((3 : ℝ) / 4)) ≤ (5619199379 : ℝ) / 1000000000000 := by
  have := rpow_neg_div_upper 1001 3 4 5619199379 1000000000000 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_neg74_hi : (((1000 : ℕ) : ℝ) + 1) ^ (-((3 : ℝ) / 4) - 1) ≤ (5613586 : ℝ) / 1000000000000 := by
  have := rpow_neg_div_upper 1001 7 4 5613586 1000000000000 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_eighth_lo : (2371669997771 : ℝ) / 1000000000000 ≤ (((1000 : ℕ) : ℝ) + 1) ^ (1 - (7 : ℝ) / 8) := by
  have := rpow_div_lower 1001 1 8 2371669997771 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_eighth_hi : (((1000 : ℕ) : ℝ) + 1) ^ (1 - (7 : ℝ) / 8) ≤ (2371669997772 : ℝ) / 1000000000000 := by
  have := rpow_div_upper 1001 1 8 2371669997772 1000000000000 (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_neg78_lo : (2369300697 : ℝ) / 1000000000000 ≤ (((1000 : ℕ) : ℝ) + 1) ^ (-((7 : ℝ) / 8)) := by
  have := rpow_neg_div_lower 1001 7 8 2369300697 1000000000000 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_neg78_hi : (((1000 : ℕ) : ℝ) + 1) ^ (-((7 : ℝ) / 8)) ≤ (2369300698 : ℝ) / 1000000000000 := by
  have := rpow_neg_div_upper 1001 7 8 2369300698 1000000000000 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_neg158_hi : (((1000 : ℕ) : ℝ) + 1) ^ (-((7 : ℝ) / 8) - 1) ≤ (2366934 : ℝ) / 1000000000000 := by
  have := rpow_neg_div_upper 1001 15 8 2366934 1000000000000 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_neg34'_lo : (5619199378 : ℝ) / 1000000000000 ≤ (((1000 : ℕ) : ℝ) + 1) ^ (1 - (7 : ℝ) / 4) := by
  have := rpow_neg_div_lower 1001 3 4 5619199378 1000000000000 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_neg34'_hi : (((1000 : ℕ) : ℝ) + 1) ^ (1 - (7 : ℝ) / 4) ≤ (5619199379 : ℝ) / 1000000000000 := by
  have := rpow_neg_div_upper 1001 3 4 5619199379 1000000000000 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_neg74'_lo : (5613585 : ℝ) / 1000000000000 ≤ (((1000 : ℕ) : ℝ) + 1) ^ (-((7 : ℝ) / 4)) := by
  have := rpow_neg_div_lower 1001 7 4 5613585 1000000000000 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_neg74'_hi : (((1000 : ℕ) : ℝ) + 1) ^ (-((7 : ℝ) / 4)) ≤ (5613586 : ℝ) / 1000000000000 := by
  have := rpow_neg_div_upper 1001 7 4 5613586 1000000000000 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

lemma n1001_neg114_hi : (((1000 : ℕ) : ℝ) + 1) ^ (-((7 : ℝ) / 4) - 1) ≤ (5608 : ℝ) / 1000000000000 := by
  have := rpow_neg_div_upper 1001 11 4 5608 1000000000000 (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  convert this using 2 <;> norm_num

/-! ### The three values -/

/-- `ζ(3/4)`: real, and `-3.44129 ≤ ζ(3/4) ≤ -3.44128`. -/
theorem riemannZeta_three_quarters :
    ∃ r : ℝ, riemannZeta (3 / 4 : ℂ) = r ∧ -3.44129 ≤ r ∧ r ≤ -3.44128 := by
  obtain ⟨R, hζ, hR0, hR1⟩ :=
    riemannZeta_ofReal_eulerMaclaurin (σ := (3 : ℝ) / 4) (by norm_num) (by norm_num) 1000
  have hζ' := hζ
  rw [show ((3 / 4 : ℝ) : ℂ) = (3 / 4 : ℂ) by norm_num] at hζ'
  rw [show ∀ X : ℝ, X / ((3 : ℝ) / 4 - 1) = (-4) * X from fun X => by ring] at hζ'
  rw [show (3 : ℝ) / 4 * (3 / 4 + 2) / 8 = 33 / 128 by norm_num] at hR1
  exact ⟨_, hζ', by linarith [zsum34_lo, n1001_quarter_hi, n1001_neg34_lo], by linarith [zsum34_hi, n1001_quarter_lo, n1001_neg34_hi, n1001_neg74_hi]⟩

/-- `ζ(7/8)`: real, and `-7.432 ≤ ζ(7/8) ≤ -7.4319`. -/
theorem riemannZeta_seven_eighths :
    ∃ r : ℝ, riemannZeta (7 / 8 : ℂ) = r ∧ -7.432 ≤ r ∧ r ≤ -7.4319 := by
  obtain ⟨R, hζ, hR0, hR1⟩ :=
    riemannZeta_ofReal_eulerMaclaurin (σ := (7 : ℝ) / 8) (by norm_num) (by norm_num) 1000
  have hζ' := hζ
  rw [show ((7 / 8 : ℝ) : ℂ) = (7 / 8 : ℂ) by norm_num] at hζ'
  rw [show ∀ X : ℝ, X / ((7 : ℝ) / 8 - 1) = (-8) * X from fun X => by ring] at hζ'
  rw [show (7 : ℝ) / 8 * (7 / 8 + 2) / 8 = 161 / 512 by norm_num] at hR1
  exact ⟨_, hζ', by linarith [zsum78_lo, n1001_eighth_hi, n1001_neg78_lo], by linarith [zsum78_hi, n1001_eighth_lo, n1001_neg78_hi, n1001_neg158_hi]⟩

/-- `ζ(7/4)`: real, and `1.96232 ≤ ζ(7/4) ≤ 1.9623202`. -/
theorem riemannZeta_seven_quarters :
    ∃ r : ℝ, riemannZeta (7 / 4 : ℂ) = r ∧ 1.96232 ≤ r ∧ r ≤ 1.9623202 := by
  obtain ⟨R, hζ, hR0, hR1⟩ :=
    riemannZeta_ofReal_eulerMaclaurin (σ := (7 : ℝ) / 4) (by norm_num) (by norm_num) 1000
  have hζ' := hζ
  rw [show ((7 / 4 : ℝ) : ℂ) = (7 / 4 : ℂ) by norm_num] at hζ'
  rw [show ∀ X : ℝ, X / ((7 : ℝ) / 4 - 1) = (4 / 3) * X from fun X => by ring] at hζ'
  rw [show (7 : ℝ) / 4 * (7 / 4 + 2) / 8 = 105 / 128 by norm_num] at hR1
  exact ⟨_, hζ', by linarith [zsum74_lo, n1001_neg34'_lo, n1001_neg74'_lo], by linarith [zsum74_hi, n1001_neg34'_hi, n1001_neg74'_hi, n1001_neg114_hi]⟩

/-- Sign facts used by the threshold argument. -/
theorem riemannZeta_three_quarters_re_neg : (riemannZeta (3 / 4 : ℂ)).re < 0 := by
  obtain ⟨r, hr, h1, h2⟩ := riemannZeta_three_quarters
  rw [hr, Complex.ofReal_re]
  linarith

theorem riemannZeta_seven_eighths_re_neg : (riemannZeta (7 / 8 : ℂ)).re < 0 := by
  obtain ⟨r, hr, h1, h2⟩ := riemannZeta_seven_eighths
  rw [hr, Complex.ofReal_re]
  linarith

theorem riemannZeta_three_quarters_im : (riemannZeta (3 / 4 : ℂ)).im = 0 := by
  obtain ⟨r, hr, -, -⟩ := riemannZeta_three_quarters
  rw [hr, Complex.ofReal_im]

theorem riemannZeta_seven_eighths_im : (riemannZeta (7 / 8 : ℂ)).im = 0 := by
  obtain ⟨r, hr, -, -⟩ := riemannZeta_seven_eighths
  rw [hr, Complex.ofReal_im]

theorem riemannZeta_seven_quarters_im : (riemannZeta (7 / 4 : ℂ)).im = 0 := by
  obtain ⟨r, hr, -, -⟩ := riemannZeta_seven_quarters
  rw [hr, Complex.ofReal_im]

end CN1.Numerics
