import CN1.Numerics.ZetaValues
import CN1.Numerics.GammaRatio
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The threshold `d ≤ 652` (step 4 of the argument)

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

At `s = 7/8` the Chowla–Selberg identity reads `ζ(7/8) L(7/8, χ₋d) = M(d) + E_d(7/8)` with the main term

  `M(d) = ζ(7/4) + 2^(3/4) √π · Γ(3/8)/Γ(7/8) · d^(-3/8) · ζ(3/4)`

and `|E_d(7/8)| ≤ B₀(d) = 4 π^(7/8) · Γ(3/8)/Γ(7/8) · (8/(π d))^(3/8) · exp(-π √d / 2)`
(`CN1.CS.B_le_B0`). This file proves, about Mathlib's `riemannZeta` and `Real.Gamma`:

* `mainTerm_655_ge`: `M(655) ≥ 0.00104` (Arb: `M(655) = 0.0011379…`; the brackets give `≥ 0.00105015`);
* `B0_655_le`: `B₀(655) ≤ 3·10⁻¹⁶`;
* `mainTerm_mono`, `B0_anti`: `M` is increasing and `B₀` decreasing on `[655, ∞)` (`ζ(3/4) < 0`);
* `mainTerm_sub_B0_pos`: `0 < M(d) - B₀(d)` for every real `d ≥ 655`;
* `disc_le_652_of_mainTerm_nonpos`: a natural `d ≡ 0, 3 (mod 4)` with `M(d) - B₀(d) ≤ 0` satisfies
  `d ≤ 652`.

The contradiction downstream (`CN1.Assembly.Core`): for a class-number-one field with `|disc| = d`,
`ζ(7/8) L(7/8, χ) ≤ 0` (`ζ(7/8) < 0`, `L(7/8, χ) ≥ 0` by `CN1.Assembly.Positivity`), while
`M(d) + E_d(7/8) ≥ M(d) - B₀(d) > 0` once `d ≥ 655`; hence `d ≤ 652` for admissible `d`. The
threshold is a statement for all real `d ≥ 655`, not only an integer scan.
-/

set_option autoImplicit false

namespace CN1.Numerics

open Real

/-- The Chowla–Selberg main term at `s = 7/8`, as a function of the real variable `d`. -/
noncomputable def mainTerm (d : ℝ) : ℝ :=
  (riemannZeta (7 / 4 : ℂ)).re
    + 2 ^ ((3 : ℝ) / 4) * √π * (Gamma (3 / 8) / Gamma (7 / 8)) * d ^ (-((3 : ℝ) / 8))
      * (riemannZeta (3 / 4 : ℂ)).re

/-- The crude remainder bound `B₀(d)` (`CN1.CS.B0`). -/
noncomputable def B0 (d : ℝ) : ℝ :=
  4 * π ^ ((7 : ℝ) / 8) * (Gamma (3 / 8) / Gamma (7 / 8)) * (8 / (π * d)) ^ ((3 : ℝ) / 8)
    * exp (-(π * √d / 2))

lemma Gamma_ratio_nonneg : 0 ≤ Gamma (3 / 8) / Gamma (7 / 8) :=
  div_nonneg (Gamma_pos_of_pos (by norm_num)).le (Gamma_pos_of_pos (by norm_num)).le

/-! ### Brackets for the constants -/

lemma two_rpow_34_lo : (168179283 : ℝ) / 100000000 ≤ (2 : ℝ) ^ ((3 : ℝ) / 4) := by
  have := rpow_div_lower 2 3 4 168179283 100000000 (by norm_num) (by norm_num) (by norm_num)
  convert this using 2
  all_goals norm_num

lemma two_rpow_34_hi : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ (168179284 : ℝ) / 100000000 := by
  have := rpow_div_upper 2 3 4 168179284 100000000 (by norm_num) (by norm_num) (by norm_num)
  convert this using 2
  all_goals norm_num

lemma d655_rpow_lo : (8788393 : ℝ) / 100000000 ≤ (655 : ℝ) ^ (-((3 : ℝ) / 8)) := by
  have := rpow_neg_div_lower 655 3 8 8788393 100000000 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  convert this using 2
  all_goals norm_num

lemma d655_rpow_hi : (655 : ℝ) ^ (-((3 : ℝ) / 8)) ≤ (8788394 : ℝ) / 100000000 := by
  have := rpow_neg_div_upper 655 3 8 8788394 100000000 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  convert this using 2
  all_goals norm_num

lemma sqrt_pi_lo : (17724536 : ℝ) / 10000000 ≤ √π := by
  rw [Real.le_sqrt (by norm_num) Real.pi_pos.le]
  have := Real.pi_gt_d6
  norm_num at this ⊢
  linarith

lemma sqrt_pi_hi : √π ≤ (17724540 : ℝ) / 10000000 := by
  rw [Real.sqrt_le_left (by norm_num)]
  have := Real.pi_lt_d6
  norm_num at this ⊢
  linarith

/-! ### The main term at `655` -/

/-- `M(655) ≥ 0.00104` (Arb: `0.0011379…`; the enclosures give `≥ 0.00105015`, so `0.00104` leaves a margin of 1e-5). -/
theorem mainTerm_655_ge : (104 : ℝ) / 100000 ≤ mainTerm 655 := by
  obtain ⟨z74, hz74, h74lo, -⟩ := riemannZeta_seven_quarters
  obtain ⟨z34, hz34, h34lo, h34hi⟩ := riemannZeta_three_quarters
  obtain ⟨-, hGhi⟩ := Gamma_ratio_enclosure
  have hG0 := Gamma_ratio_nonneg
  unfold mainTerm
  rw [hz74, hz34, Complex.ofReal_re, Complex.ofReal_re]
  set G := Gamma (3 / 8) / Gamma (7 / 8) with hG
  have hP : 2 ^ ((3 : ℝ) / 4) * √π * G * (655 : ℝ) ^ (-((3 : ℝ) / 8))
      ≤ (168179284 : ℝ) / 100000000 * ((17724540 : ℝ) / 10000000) * 2.1755
        * ((8788394 : ℝ) / 100000000) := by
    have h1 := two_rpow_34_hi
    have h2 := sqrt_pi_hi
    have h3 := d655_rpow_hi
    gcongr
  have h1 : (168179284 : ℝ) / 100000000 * ((17724540 : ℝ) / 10000000) * 2.1755
      * ((8788394 : ℝ) / 100000000) * z34
      ≤ 2 ^ ((3 : ℝ) / 4) * √π * G * (655 : ℝ) ^ (-((3 : ℝ) / 8)) * z34 :=
    mul_le_mul_of_nonpos_right hP (by linarith)
  have h2 : (168179284 : ℝ) / 100000000 * ((17724540 : ℝ) / 10000000) * 2.1755
      * ((8788394 : ℝ) / 100000000) * (-3.44129)
      ≤ (168179284 : ℝ) / 100000000 * ((17724540 : ℝ) / 10000000) * 2.1755
      * ((8788394 : ℝ) / 100000000) * z34 :=
    mul_le_mul_of_nonneg_left h34lo (by norm_num)
  linarith

/-! ### The remainder bound at `655` -/

/-- `B₀(655) ≤ 3·10⁻¹⁶`. -/
theorem B0_655_le : B0 655 ≤ (3 : ℝ) / 10 ^ 16 := by
  obtain ⟨-, hGhi⟩ := Gamma_ratio_enclosure
  have hG0 := Gamma_ratio_nonneg
  unfold B0
  set G := Gamma (3 / 8) / Gamma (7 / 8) with hG
  have hpi : π ^ ((7 : ℝ) / 8) ≤ 3.15 := by
    calc π ^ ((7 : ℝ) / 8) ≤ π ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by norm_num)
      _ = π := Real.rpow_one π
      _ ≤ 3.15 := by linarith [Real.pi_lt_d6]
  have hx : (8 / (π * 655) : ℝ) ^ ((3 : ℝ) / 8) ≤ 1 := by
    apply Real.rpow_le_one (by positivity) _ (by norm_num)
    rw [div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  have hexp : exp (-(π * √655 / 2)) ≤ 1 / 10 ^ 17 := by
    have hs : (25.5 : ℝ) ≤ √655 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have h1 : (40 : ℝ) ≤ π * √655 / 2 := by
      have := Real.pi_gt_d6
      nlinarith
    have h2 : exp (-(π * √655 / 2)) ≤ exp (-40) := exp_le_exp.mpr (by linarith)
    have h3 : (10 : ℝ) ^ 17 ≤ exp 40 := by
      have he := Real.exp_one_gt_d9
      calc (10 : ℝ) ^ 17 ≤ 2.7182818283 ^ 40 := by norm_num
        _ ≤ exp 1 ^ 40 := by gcongr
        _ = exp 40 := by rw [← Real.exp_nat_mul]; norm_num
    calc exp (-(π * √655 / 2)) ≤ exp (-40) := h2
      _ = 1 / exp 40 := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / 10 ^ 17 := by gcongr
  have hE0 : 0 ≤ exp (-(π * √655 / 2)) := (exp_pos _).le
  have hX0 : 0 ≤ (8 / (π * 655) : ℝ) ^ ((3 : ℝ) / 8) := by positivity
  have hpi0 : 0 ≤ π ^ ((7 : ℝ) / 8) := by positivity
  calc 4 * π ^ ((7 : ℝ) / 8) * G * (8 / (π * 655)) ^ ((3 : ℝ) / 8) * exp (-(π * √655 / 2))
      ≤ 4 * 3.15 * 2.1755 * 1 * (1 / 10 ^ 17) := by gcongr
    _ ≤ (3 : ℝ) / 10 ^ 16 := by norm_num

/-! ### Monotonicity in `d` -/

/-- `M` is increasing on `[655, ∞)`, because `ζ(3/4) < 0` and `d^(-3/8)` is decreasing. -/
theorem mainTerm_mono {d : ℝ} (hd : 655 ≤ d) : mainTerm 655 ≤ mainTerm d := by
  obtain ⟨z34, hz34, -, h34hi⟩ := riemannZeta_three_quarters
  have hG0 := Gamma_ratio_nonneg
  unfold mainTerm
  rw [hz34, Complex.ofReal_re]
  set G := Gamma (3 / 8) / Gamma (7 / 8) with hG
  have hC : 0 ≤ 2 ^ ((3 : ℝ) / 4) * √π * G :=
    mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) hG0
  have hpow : d ^ (-((3 : ℝ) / 8)) ≤ (655 : ℝ) ^ (-((3 : ℝ) / 8)) :=
    (Real.rpow_le_rpow_iff_of_neg (by linarith) (by norm_num) (by norm_num)).mpr hd
  have h1 : 2 ^ ((3 : ℝ) / 4) * √π * G * d ^ (-((3 : ℝ) / 8))
      ≤ 2 ^ ((3 : ℝ) / 4) * √π * G * (655 : ℝ) ^ (-((3 : ℝ) / 8)) :=
    mul_le_mul_of_nonneg_left hpow hC
  have h2 := mul_le_mul_of_nonpos_right h1 (by linarith : z34 ≤ 0)
  linarith

/-- `B₀` is decreasing on `[655, ∞)`. -/
theorem B0_anti {d : ℝ} (hd : 655 ≤ d) : B0 d ≤ B0 655 := by
  have hG0 := Gamma_ratio_nonneg
  unfold B0
  set G := Gamma (3 / 8) / Gamma (7 / 8) with hG
  have hd0 : (0 : ℝ) < d := by linarith
  have hx : (8 / (π * d)) ^ ((3 : ℝ) / 8) ≤ (8 / (π * 655)) ^ ((3 : ℝ) / 8) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    gcongr
  have he : exp (-(π * √d / 2)) ≤ exp (-(π * √655 / 2)) := by
    apply exp_le_exp.mpr
    have := Real.sqrt_le_sqrt hd
    nlinarith [Real.pi_pos]
  have hA : 0 ≤ 4 * π ^ ((7 : ℝ) / 8) * G := mul_nonneg (by positivity) hG0
  calc 4 * π ^ ((7 : ℝ) / 8) * G * (8 / (π * d)) ^ ((3 : ℝ) / 8) * exp (-(π * √d / 2))
      ≤ 4 * π ^ ((7 : ℝ) / 8) * G * (8 / (π * 655)) ^ ((3 : ℝ) / 8) * exp (-(π * √d / 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hA) (exp_pos _).le
    _ ≤ 4 * π ^ ((7 : ℝ) / 8) * G * (8 / (π * 655)) ^ ((3 : ℝ) / 8) * exp (-(π * √655 / 2)) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg hA (by positivity))

/-! ### The threshold -/

/-- **The threshold.** For every real `d ≥ 655`, `M(d) - B₀(d) > 0`. -/
theorem mainTerm_sub_B0_pos {d : ℝ} (hd : 655 ≤ d) : 0 < mainTerm d - B0 d := by
  have h1 := mainTerm_mono hd
  have h2 := B0_anti hd
  have h3 := mainTerm_655_ge
  have h4 := B0_655_le
  linarith

/-- A natural `d ≡ 0, 3 (mod 4)` with `M(d) - B₀(d) ≤ 0` satisfies `d ≤ 652`. -/
theorem disc_le_652_of_mainTerm_nonpos (d : ℕ) (hd4 : d % 4 = 0 ∨ d % 4 = 3)
    (h : mainTerm d - B0 d ≤ 0) : d ≤ 652 := by
  by_contra hcon
  have h655 : (655 : ℝ) ≤ d := by
    have : 655 ≤ d := by omega
    exact_mod_cast this
  linarith [mainTerm_sub_B0_pos h655]

end CN1.Numerics
