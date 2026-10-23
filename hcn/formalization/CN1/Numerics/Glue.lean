import CN1.Numerics.Threshold
import CN1.ChowlaSelberg.SevenEighths

/-!
# Glue: the threshold in the exact terms of `CN1.ChowlaSelberg`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Imports `CN1.ChowlaSelberg.SevenEighths`
(Mathlib-only closure) and `CN1.Numerics.Threshold`.

`CN1.CS.CS_seven_eighths_zeta_mul` writes the main term as
`ζ(7/4) + (π^(7/8) Γ(3/8)/Γ(7/8) (4/(πd))^(3/8) : ℝ) ζ(3/4)` and bounds `|re E_d(7/8)| ≤ CS.B0 d`.
Here:
* `coeff_eq`: `π^(7/8) Γ(3/8)/Γ(7/8) (4/(πd))^(3/8) = 2^(3/4) √π (Γ(3/8)/Γ(7/8)) d^(-3/8)`, so that main term is
  `mainTerm d`, and `CS.B0 d = B0 d`;
* `CS_mainTerm_sub_B0_pos`: for `d ≥ 655`, `0 < ζ(7/4) + coeff · ζ(3/4) - CS.B0 d` in that shape;
* `disc_le_652_of_CS`: the whole contradiction for the assembly (`CN1.Assembly.Core`): if
  `ζ(s) L(s) = ½ Z_d(s)` on `re s > 1` for some `L` holomorphic on `re s > 1/2` with `L(7/8)` real
  and `≥ 0` (`CN1.Assembly.Positivity`), then `d ≤ 652`.
-/

set_option autoImplicit false

namespace CN1.Numerics

open Real

/-- The coefficient identity `π^(7/8) (4/(πd))^(3/8) = 2^(3/4) √π d^(-3/8)` for `d > 0`. -/
lemma coeff_eq {d : ℝ} (hd : 0 < d) :
    π ^ ((7 : ℝ) / 8) * Gamma (3 / 8) / Gamma (7 / 8) * (4 / (π * d)) ^ ((3 : ℝ) / 8)
      = 2 ^ ((3 : ℝ) / 4) * √π * (Gamma (3 / 8) / Gamma (7 / 8)) * d ^ (-((3 : ℝ) / 8)) := by
  have hpi := Real.pi_pos
  have h4 : (4 : ℝ) ^ ((3 : ℝ) / 8) = 2 ^ ((3 : ℝ) / 4) := by
    conv_lhs => rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have h1 : (4 / (π * d)) ^ ((3 : ℝ) / 8) = 2 ^ ((3 : ℝ) / 4) * π ^ (-((3 : ℝ) / 8)) * d ^ (-((3 : ℝ) / 8)) := by
    rw [Real.div_rpow (by norm_num) (by positivity), Real.mul_rpow hpi.le hd.le,
      Real.rpow_neg hpi.le, Real.rpow_neg hd.le, h4]
    ring
  have h2 : π ^ ((7 : ℝ) / 8) * π ^ (-((3 : ℝ) / 8)) = √π := by
    rw [← Real.rpow_add hpi, Real.sqrt_eq_rpow]
    norm_num
  rw [h1]
  calc π ^ ((7 : ℝ) / 8) * Gamma (3 / 8) / Gamma (7 / 8)
        * (2 ^ ((3 : ℝ) / 4) * π ^ (-((3 : ℝ) / 8)) * d ^ (-((3 : ℝ) / 8)))
      = 2 ^ ((3 : ℝ) / 4) * (π ^ ((7 : ℝ) / 8) * π ^ (-((3 : ℝ) / 8))) * (Gamma (3 / 8) / Gamma (7 / 8))
        * d ^ (-((3 : ℝ) / 8)) := by ring
    _ = _ := by rw [h2]

/-- The Chowla–Selberg main term at `7/8` is `mainTerm d`. -/
lemma mainTerm_eq_CS (d : ℕ) (hd : 1 ≤ d) :
    (riemannZeta (7 / 4 : ℂ)).re
      + (π ^ ((7 : ℝ) / 8) * Gamma (3 / 8) / Gamma (7 / 8) * (4 / (π * d)) ^ ((3 : ℝ) / 8))
        * (riemannZeta (3 / 4 : ℂ)).re = mainTerm d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [mainTerm, coeff_eq hd']

/-- `CN1.CS.B0 d` is `B0 d`. -/
lemma B0_eq_CS (d : ℕ) : CN1.CS.B0 d = B0 d := by
  unfold CN1.CS.B0 B0
  ring

/-- **The threshold in the shape of `CN1.CS.CS_seven_eighths_zeta_mul`.** -/
theorem CS_mainTerm_sub_B0_pos (d : ℕ) (hd : 655 ≤ d) :
    0 < (riemannZeta (7 / 4 : ℂ)).re
      + (π ^ ((7 : ℝ) / 8) * Gamma (3 / 8) / Gamma (7 / 8) * (4 / (π * d)) ^ ((3 : ℝ) / 8))
        * (riemannZeta (3 / 4 : ℂ)).re - CN1.CS.B0 d := by
  rw [mainTerm_eq_CS d (by omega), B0_eq_CS]
  exact mainTerm_sub_B0_pos (by exact_mod_cast hd)

/-- **The contradiction for the assembly.** If `ζ(s) L(s) = ½ Z_d(s)` on `re s > 1` for an `L`
holomorphic on `re s > 1/2` with `L(7/8)` real and nonnegative (`CN1.Assembly.Positivity` for `χ₋d`),
then `d ≤ 652`. -/
theorem disc_le_652_of_CS (d : ℕ) (hd : CN1.CS.IsDisc d) (h7 : 7 ≤ d) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 / 2 < s.re})
    (hZ : ∀ s : ℂ, 1 < s.re → riemannZeta s * L s = (1 / 2 : ℂ) * CN1.CS.Z d s)
    (hLim : (L (7 / 8)).im = 0) (hLre : 0 ≤ (L (7 / 8)).re) : d ≤ 652 := by
  have hCS := CN1.CS.CS_seven_eighths_zeta_mul hd (by omega) hL hZ
  have hE := CN1.CS.abs_E_seven_eighths_re_le_B0 h7
  have hz78 := riemannZeta_seven_eighths_re_neg
  have hz78i := riemannZeta_seven_eighths_im
  -- real parts of both sides
  have hre := congrArg Complex.re hCS
  rw [Complex.mul_re, hz78i, hLim, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul] at hre
  -- left side ≤ 0
  have hleft : (riemannZeta (7 / 8 : ℂ)).re * (L (7 / 8)).re - 0 * 0 ≤ 0 := by
    nlinarith
  have hEre := (abs_le.mp hE).1
  have hmain : mainTerm d - B0 d ≤ 0 := by
    rw [← mainTerm_eq_CS d (by omega), ← B0_eq_CS]
    linarith
  exact disc_le_652_of_mainTerm_nonpos d hd hmain

end CN1.Numerics
