import HCN.Statements.GeneralCS
import CN1.Numerics.ZetaValues
import CN1.Numerics.GammaRatio
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# HCN.Numerics.Threshold: the numerics of the threshold `h ≤ 2 ⇒ d ≤ 4777`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Imports only the DEFINITIONS of `HCN.Statements.GeneralCS`
(`Bg`, `cstg`); no theorem of that file is used here, so nothing below depends on a `sorry`.

At `s = 7/8` a class with leading coefficient `a ∈ [1, aₘ]`, `aₘ = (2/3)√D`, contributes (from
`mainTermg_seven_eighths`, `norm_Eg_seven_eighths_le`, `Bg_mono`; assembled in `HCN.Assembly.LowerBound`)

  `a^{-7/8} ζ(7/4) + coeffg a D · ζ(3/4) + re E ≥ a^{-7/8} ζ(7/4) + coeffg 1 D · ζ(3/4) - Bg(aₘ, D)`.

For the principal class (`a = 1`) this is `Pv D`; for every class it is at least `Tv D` (with `a^{-7/8} ≥ aₘ^{-7/8}`).
This file proves, about Mathlib's `riemannZeta`, `Real.Gamma`, `Real.exp`, `Real.sqrt`, `Real.rpow`:

* `Pv_pos_and_add_Tv_pos`: `0 < Pv D` and `0 < Pv D + Tv D` for every real `D ≥ 4778`.

**Why the non-principal `y = 0` term is kept.** A simpler bound drops the non-principal `y = 0` term
`a^{-7/8} ζ(7/4) > 0`. Without it the margin at `D = 4778` is `+2.05e-5` exactly, which CN-1's proved enclosure
`Γ(3/8)/Γ(7/8) ∈ [2.1753, 2.1755]` cannot resolve (worst case `-6.7e-5`). Keeping it (`Tv`) gives the
margin `0.0687`. The theorem proved downstream is still exactly `h ≤ 2 ⇒ dOf m ≤ 4777`.

**One evaluation covers all `D ≥ 4778`.** With `e = D^{1/16}`: `√D = e⁸`, `cstg(aₘ, D) = 3π/4` exactly, and
`coeffg 1 D = k₁ e⁻⁶`, `aₘ^{-7/8} = (2/3)^{-7/8} e⁻⁷`, `Bg(aₘ, D) = κ e⁻⁷` with constants `k₁, κ`. So
`Pv + Tv = ζ(7/4) + 2 k₁ ζ(3/4) e⁻⁶ + ((2/3)^{-7/8} ζ(7/4) - 2κ) e⁻⁷`, and `e⁻⁶ ≤ 4778^{-3/8}`, `e⁻⁷ ≤ 4778^{-7/16}`.

The rational brackets are checked here by `norm_num`.
-/

set_option autoImplicit false

namespace HCN.Numerics

open Real HCN.CS

/-! ### Definitions -/

/-- The coefficient of `ζ(3/4)` in `mainTermg_seven_eighths`, with `disc a b c` replaced by `D`. -/
noncomputable def coeffg (a D : ℝ) : ℝ :=
  π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * (Real.sqrt a)⁻¹ * (4 * a / (π * D)) ^ (3 / 8 : ℝ)

/-- The principal-class lower bound at `s = 7/8`: `ζ(7/4) + coeffg 1 D · ζ(3/4) - Bg((2/3)√D, D)`. -/
noncomputable def Pv (D : ℝ) : ℝ :=
  (riemannZeta (7 / 4 : ℂ)).re + coeffg 1 D * (riemannZeta (3 / 4 : ℂ)).re - Bg (2 / 3 * Real.sqrt D) D

/-- The any-class lower bound at `s = 7/8`: `aₘ^{-7/8} ζ(7/4) + coeffg 1 D · ζ(3/4) - Bg(aₘ, D)`, `aₘ = (2/3)√D`. -/
noncomputable def Tv (D : ℝ) : ℝ :=
  (2 / 3 * Real.sqrt D) ^ (-(7 / 8 : ℝ)) * (riemannZeta (7 / 4 : ℂ)).re
    + coeffg 1 D * (riemannZeta (3 / 4 : ℂ)).re - Bg (2 / 3 * Real.sqrt D) D

/-! ### Rational brackets for `x ^ r` -/

/-- `x^k ≤ U^n` and `r·n = k` give `x^r ≤ U`. -/
lemma rpow_le_of_pow_le {x U r : ℝ} {k n : ℕ} (hx : 0 ≤ x) (hU : 0 ≤ U) (hn : n ≠ 0)
    (hr : r * n = k) (h : x ^ k ≤ U ^ n) : x ^ r ≤ U := by
  have hxr : (x ^ r) ^ n = x ^ k := by
    rw [← Real.rpow_natCast (x ^ r), ← Real.rpow_mul hx, hr, Real.rpow_natCast]
  rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg hx r) hU hn, hxr]
  exact h

/-- `L^n ≤ x^k` and `r·n = k` give `L ≤ x^r`. -/
lemma le_rpow_of_le_pow {x L r : ℝ} {k n : ℕ} (hx : 0 ≤ x) (hL : 0 ≤ L) (hn : n ≠ 0)
    (hr : r * n = k) (h : L ^ n ≤ x ^ k) : L ≤ x ^ r := by
  have hxr : (x ^ r) ^ n = x ^ k := by
    rw [← Real.rpow_natCast (x ^ r), ← Real.rpow_mul hx, hr, Real.rpow_natCast]
  rw [← pow_le_pow_iff_left₀ hL (Real.rpow_nonneg hx r) hn, hxr]
  exact h

/-- `(e^k)^r = e^j` when `k·r = j`. -/
lemma pow_rpow_eq {e : ℝ} (he : 0 ≤ e) {k j : ℕ} {r : ℝ} (h : (k : ℝ) * r = j) : (e ^ k) ^ r = e ^ j := by
  rw [← Real.rpow_natCast e k, ← Real.rpow_mul he, h, Real.rpow_natCast]

/-- `(e^k)^r = (e^j)⁻¹` when `k·r = -j`. -/
lemma pow_rpow_eq_inv {e : ℝ} (he : 0 ≤ e) {k j : ℕ} {r : ℝ} (h : (k : ℝ) * r = -j) :
    (e ^ k) ^ r = (e ^ j)⁻¹ := by
  rw [← Real.rpow_natCast e k, ← Real.rpow_mul he, h, Real.rpow_neg he, Real.rpow_natCast]

lemma pi_rpow_78_le : π ^ (7 / 8 : ℝ) ≤ 6807 / 2500 := by
  have h1 : π ^ (7 / 8 : ℝ) ≤ (3.141593 : ℝ) ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow Real.pi_pos.le Real.pi_lt_d6.le (by norm_num)
  have h2 : (3.141593 : ℝ) ^ (7 / 8 : ℝ) ≤ 6807 / 2500 :=
    rpow_le_of_pow_le (k := 7) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

lemma four_div_pi_rpow_le : (4 / π) ^ (3 / 8 : ℝ) ≤ 10949 / 10000 := by
  have h0 : 4 / π ≤ 4 / (3.141592 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) Real.pi_gt_d6.le
  have h1 : (4 / π) ^ (3 / 8 : ℝ) ≤ (4 / (3.141592 : ℝ)) ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow (by positivity) h0 (by norm_num)
  have h2 : (4 / (3.141592 : ℝ)) ^ (3 / 8 : ℝ) ≤ 10949 / 10000 :=
    rpow_le_of_pow_le (k := 3) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

lemma sixteen_div_rpow_le : (16 / (3 * π)) ^ (3 / 8 : ℝ) ≤ 3049 / 2500 := by
  have h0 : 16 / (3 * π) ≤ 16 / (3 * (3.141592 : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [Real.pi_gt_d6])
  have h1 : (16 / (3 * π)) ^ (3 / 8 : ℝ) ≤ (16 / (3 * (3.141592 : ℝ))) ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow (by positivity) h0 (by norm_num)
  have h2 : (16 / (3 * (3.141592 : ℝ))) ^ (3 / 8 : ℝ) ≤ 3049 / 2500 :=
    rpow_le_of_pow_le (k := 3) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith

lemma sqrt_two_thirds_ge : (2041 / 2500 : ℝ) ≤ Real.sqrt (2 / 3) := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

lemma two_thirds_rpow_neg_ge : (5000 / 3507 : ℝ) ≤ (2 / 3 : ℝ) ^ (-(7 / 8 : ℝ)) := by
  have h1 : (2 / 3 : ℝ) ^ (7 / 8 : ℝ) ≤ 3507 / 5000 :=
    rpow_le_of_pow_le (k := 7) (n := 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h0 : 0 < (2 / 3 : ℝ) ^ (7 / 8 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.rpow_neg (by norm_num)]
  calc (5000 / 3507 : ℝ) = (3507 / 5000)⁻¹ := by norm_num
    _ ≤ ((2 / 3 : ℝ) ^ (7 / 8 : ℝ))⁻¹ := inv_anti₀ h0 h1

/-- `e^{-3π/4} ≤ 0.09534` (true value `0.0947802…`). -/
lemma exp_neg_three_pi_div_four_le : Real.exp (-(3 * π / 4)) ≤ 4767 / 50000 := by
  have hx : (2.356194 : ℝ) ≤ 3 * π / 4 := by linarith [Real.pi_gt_d6]
  have he1 := Real.exp_one_gt_d9
  have hq := Real.quadratic_le_exp_of_nonneg (x := (0.356194 : ℝ)) (by norm_num)
  have hexp : (2.7182818283 : ℝ) ^ 2 * (1 + 0.356194 + 0.356194 ^ 2 / 2) ≤ Real.exp 2.356194 := by
    have : Real.exp 2.356194 = Real.exp 1 * Real.exp 1 * Real.exp 0.356194 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [this, sq]
    gcongr
  have hlo : (50000 / 4767 : ℝ) ≤ Real.exp (3 * π / 4) :=
    le_trans (by norm_num) (hexp.trans (Real.exp_le_exp.mpr hx))
  rw [Real.exp_neg]
  calc (Real.exp (3 * π / 4))⁻¹ ≤ (50000 / 4767 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hlo
    _ = 4767 / 50000 := by norm_num

/-! ### The `e = D^{1/16}` normal form -/

section ENormal

variable {e : ℝ} (he : 0 < e)
include he

lemma sqrt_e16 : Real.sqrt (e ^ 16) = e ^ 8 := by
  rw [show e ^ 16 = (e ^ 8) ^ 2 by ring, Real.sqrt_sq (by positivity)]

lemma amax_rpow_eq : (2 / 3 * e ^ 8) ^ (-(7 / 8 : ℝ)) = (2 / 3 : ℝ) ^ (-(7 / 8 : ℝ)) * (e ^ 7)⁻¹ := by
  rw [Real.mul_rpow (by norm_num) (by positivity), pow_rpow_eq_inv he.le (j := 7) (by norm_num)]

lemma coeffg_one_eq : coeffg 1 (e ^ 16) =
    π ^ (7 / 8 : ℝ) * (Real.Gamma (3 / 8) / Real.Gamma (7 / 8)) * (4 / π) ^ (3 / 8 : ℝ) * (e ^ 6)⁻¹ := by
  have h : 4 * 1 / (π * e ^ 16) = (4 / π) * (e ^ 16)⁻¹ := by
    field_simp
  rw [coeffg, h, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
    pow_rpow_eq he.le (j := 6) (by norm_num), Real.sqrt_one, inv_one]
  ring

/-- The remainder bound at `aₘ = (2/3)√D`, `D = e^16`: `cstg = 3π/4` and `Bg(aₘ, D) = κ e⁻⁷`. -/
lemma Bg_amax_eq : Bg (2 / 3 * e ^ 8) (e ^ 16) =
    2 * π ^ (7 / 8 : ℝ) * (Real.Gamma (3 / 8) / Real.Gamma (7 / 8)) * (Real.sqrt (2 / 3))⁻¹ *
      (16 / (3 * π)) ^ (3 / 8 : ℝ) *
      (Real.exp (-(3 * π / 4)) / (1 - Real.exp (-(3 * π / 4))) ^ 2) * (e ^ 7)⁻¹ := by
  have hc : cstg (2 / 3 * e ^ 8) (e ^ 16) = 3 * π / 4 := by
    rw [cstg, sqrt_e16 he]
    field_simp
    ring
  have hs : Real.sqrt (2 / 3 * e ^ 8) = Real.sqrt (2 / 3) * e ^ 4 := by
    rw [Real.sqrt_mul (by norm_num), show e ^ 8 = (e ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h8 : 8 * (2 / 3 * e ^ 8) / (π * e ^ 16) = (16 / (3 * π)) * (e ^ 8)⁻¹ := by
    field_simp
    ring
  rw [Bg, hc, hs, h8, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
    pow_rpow_eq he.le (j := 3) (by norm_num)]
  field_simp

end ENormal

/-! ### The threshold inequalities -/

/-- The `e`-form of both inequalities, for `e > 0` with `e^16 ≥ 4778`. -/
theorem pos_of_e {e : ℝ} (he : 0 < e) (h16 : 4778 ≤ e ^ 16) :
    0 < Pv (e ^ 16) ∧ 0 < Pv (e ^ 16) + Tv (e ^ 16) := by
  obtain ⟨z74, hz74, h74lo, -⟩ := CN1.Numerics.riemannZeta_seven_quarters
  obtain ⟨z34, hz34, h34lo, h34hi⟩ := CN1.Numerics.riemannZeta_three_quarters
  obtain ⟨hGlo, hGhi⟩ := CN1.Numerics.Gamma_ratio_enclosure
  unfold Pv Tv
  rw [hz74, hz34, Complex.ofReal_re, Complex.ofReal_re, sqrt_e16 he, amax_rpow_eq he, coeffg_one_eq he,
    Bg_amax_eq he]
  set G := Real.Gamma (3 / 8) / Real.Gamma (7 / 8) with hG
  set p78 := π ^ (7 / 8 : ℝ)
  set c4 := (4 / π) ^ (3 / 8 : ℝ)
  set c16 := (16 / (3 * π)) ^ (3 / 8 : ℝ)
  set s23 := Real.sqrt (2 / 3)
  set q := Real.exp (-(3 * π / 4))
  set a78 := (2 / 3 : ℝ) ^ (-(7 / 8 : ℝ))
  set w6 := (e ^ 6)⁻¹
  set w7 := (e ^ 7)⁻¹
  -- the brackets
  have hp78 : p78 ≤ 6807 / 2500 := pi_rpow_78_le
  have hp78' : 0 ≤ p78 := by positivity
  have hc4 : c4 ≤ 10949 / 10000 := four_div_pi_rpow_le
  have hc4' : 0 ≤ c4 := by positivity
  have hc16 : c16 ≤ 3049 / 2500 := sixteen_div_rpow_le
  have hc16' : 0 ≤ c16 := by positivity
  have hs23 : (2041 / 2500 : ℝ) ≤ s23 := sqrt_two_thirds_ge
  have hs23i : s23⁻¹ ≤ 2500 / 2041 := by
    calc s23⁻¹ ≤ (2041 / 2500 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hs23
      _ = 2500 / 2041 := by norm_num
  have hs23i' : 0 ≤ s23⁻¹ := by positivity
  have hq : q ≤ 4767 / 50000 := exp_neg_three_pi_div_four_le
  have hq0 : 0 < q := Real.exp_pos _
  have ha78 : (5000 / 3507 : ℝ) ≤ a78 := two_thirds_rpow_neg_ge
  have hG0 : 0 ≤ G := le_trans (by norm_num) hGlo
  -- `K = q/(1-q)^2 ≤ Q/(1-Q)^2`
  have hK : q / (1 - q) ^ 2 ≤ (4767 / 50000) / (1 - 4767 / 50000) ^ 2 := by
    have h1 : q / (1 - q) ^ 2 ≤ (4767 / 50000) / (1 - q) ^ 2 :=
      div_le_div_of_nonneg_right hq (by positivity)
    have h2 : (4767 / 50000 : ℝ) / (1 - q) ^ 2 ≤ (4767 / 50000) / (1 - 4767 / 50000) ^ 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have : (1 - 4767 / 50000 : ℝ) ≤ 1 - q := by linarith
      nlinarith
    linarith
  have hK0 : 0 ≤ q / (1 - q) ^ 2 := by
    have : 0 < 1 - q := by linarith
    positivity
  -- `e^{-6} ≤ 4778^{-3/8}`, `e^{-7} ≤ 4778^{-7/16}`
  have hw6 : w6 ≤ 41721 / 1000000 := by
    have h8 : ((1000000 : ℝ) / 41721) ^ 8 ≤ (e ^ 6) ^ 8 := by
      calc ((1000000 : ℝ) / 41721) ^ 8 ≤ (4778 : ℝ) ^ 3 := by norm_num
        _ ≤ (e ^ 16) ^ 3 := by gcongr
        _ = (e ^ 6) ^ 8 := by ring
    have h6 : (1000000 : ℝ) / 41721 ≤ e ^ 6 :=
      (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num)).mp h8
    calc w6 ≤ ((1000000 : ℝ) / 41721)⁻¹ := inv_anti₀ (by norm_num) h6
      _ = 41721 / 1000000 := by norm_num
  have hw7 : w7 ≤ 24567 / 1000000 := by
    have h16' : ((1000000 : ℝ) / 24567) ^ 16 ≤ (e ^ 7) ^ 16 := by
      calc ((1000000 : ℝ) / 24567) ^ 16 ≤ (4778 : ℝ) ^ 7 := by norm_num
        _ ≤ (e ^ 16) ^ 7 := by gcongr
        _ = (e ^ 7) ^ 16 := by ring
    have h7 : (1000000 : ℝ) / 24567 ≤ e ^ 7 :=
      (pow_le_pow_iff_left₀ (by norm_num) (by positivity) (by norm_num)).mp h16'
    calc w7 ≤ ((1000000 : ℝ) / 24567)⁻¹ := inv_anti₀ (by norm_num) h7
      _ = 24567 / 1000000 := by norm_num
  have hw6' : 0 ≤ w6 := by positivity
  have hw7' : 0 ≤ w7 := by positivity
  -- `m₆ = k₁ e⁻⁶ ≤ k₁⁺ · 4778^{-3/8}`, and `κ e⁻⁷ ≤ κ⁺ · 4778^{-7/16}`
  have hm6 : p78 * G * c4 * w6 ≤ 6807 / 2500 * 2.1755 * (10949 / 10000) * (41721 / 1000000) := by
    gcongr
  have hm6' : 0 ≤ p78 * G * c4 * w6 := by positivity
  have hkap : 2 * p78 * G * s23⁻¹ * c16 * (q / (1 - q) ^ 2) ≤
      2 * (6807 / 2500) * 2.1755 * (2500 / 2041) * (3049 / 2500) *
        ((4767 / 50000) / (1 - 4767 / 50000) ^ 2) := by
    gcongr
  have hkap' : 0 ≤ 2 * p78 * G * s23⁻¹ * c16 * (q / (1 - q) ^ 2) := by positivity
  set m6 := p78 * G * c4 * w6 with hm6def
  set kap := 2 * p78 * G * s23⁻¹ * c16 * (q / (1 - q) ^ 2) with hkapdef
  have hcoef : p78 * G * c4 * w6 * z34 = m6 * z34 := rfl
  have hkw : kap * w7 ≤ 2 * (6807 / 2500) * 2.1755 * (2500 / 2041) * (3049 / 2500) *
      ((4767 / 50000) / (1 - 4767 / 50000) ^ 2) * (24567 / 1000000) := by
    gcongr
  have hkw' : 0 ≤ kap * w7 := by positivity
  have hm6z : 6807 / 2500 * 2.1755 * (10949 / 10000) * (41721 / 1000000) * (-3.44129 : ℝ) ≤ m6 * z34 := by
    nlinarith
  -- the `y = 0` term of a non-principal class against twice the remainder: `(a₇₈ ζ(7/4) - 2κ) e⁻⁷`
  have hbeta : (5000 / 3507 * 1.96232 - 2 * (2 * (6807 / 2500) * 2.1755 * (2500 / 2041) * (3049 / 2500) *
      ((4767 / 50000) / (1 - 4767 / 50000) ^ 2))) * (24567 / 1000000) ≤ (a78 * z74 - 2 * kap) * w7 := by
    have hlo : (5000 / 3507 * 1.96232 : ℝ) ≤ a78 * z74 := by
      have : (0 : ℝ) ≤ 5000 / 3507 := by norm_num
      nlinarith
    rcases le_or_gt 0 (a78 * z74 - 2 * kap) with hb | hb
    · have : 0 ≤ (a78 * z74 - 2 * kap) * w7 := mul_nonneg hb hw7'
      have : (5000 / 3507 * 1.96232 - 2 * (2 * (6807 / 2500) * 2.1755 * (2500 / 2041) * (3049 / 2500) *
          ((4767 / 50000) / (1 - 4767 / 50000) ^ 2))) * (24567 / 1000000 : ℝ) ≤ 0 := by norm_num
      linarith
    · have h1 : (a78 * z74 - 2 * kap) * (24567 / 1000000) ≤ (a78 * z74 - 2 * kap) * w7 :=
        mul_le_mul_of_nonpos_left hw7 hb.le
      nlinarith
  constructor
  · have e1 : z74 + p78 * G * c4 * w6 * z34 - 2 * p78 * G * s23⁻¹ * c16 * (q / (1 - q) ^ 2) * w7
        = z74 + m6 * z34 - kap * w7 := rfl
    rw [e1]
    norm_num at hm6z hkw ⊢
    linarith
  · have e2 : z74 + p78 * G * c4 * w6 * z34 - 2 * p78 * G * s23⁻¹ * c16 * (q / (1 - q) ^ 2) * w7 +
        (a78 * w7 * z74 + p78 * G * c4 * w6 * z34 - 2 * p78 * G * s23⁻¹ * c16 * (q / (1 - q) ^ 2) * w7)
        = z74 + 2 * (m6 * z34) + (a78 * z74 - 2 * kap) * w7 := by
      rw [hm6def, hkapdef]; ring
    rw [e2]
    norm_num at hm6z hbeta ⊢
    linarith

/-- **The threshold numerics.** For every real `D ≥ 4778`: `0 < Pv D` and `0 < Pv D + Tv D`. -/
theorem Pv_pos_and_add_Tv_pos {D : ℝ} (hD : 4778 ≤ D) : 0 < Pv D ∧ 0 < Pv D + Tv D := by
  have hD0 : 0 ≤ D := by linarith
  set e := D ^ ((16 : ℕ)⁻¹ : ℝ) with he
  have he16 : e ^ 16 = D := Real.rpow_inv_natCast_pow hD0 (by norm_num)
  have he0 : 0 < e := Real.rpow_pos_of_pos (by linarith) _
  rw [← he16] at hD ⊢
  exact pos_of_e he0 hD

end HCN.Numerics
