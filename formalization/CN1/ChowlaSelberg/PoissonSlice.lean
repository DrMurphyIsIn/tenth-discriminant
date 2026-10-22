import CN1.ChowlaSelberg.Form
import CN1.ChowlaSelberg.GammaIntegral

/-!
# CN1.ChowlaSelberg.PoissonSlice: the Poisson slice lemma

For fixed `y ≠ 0` and `re s > 1`,

  `Σ_x Q(x, y)^{-s} = (π^s / Γ(s)) Σ_{k ∈ ℤ} (-1)^{k b y} I(s; π d y²/4, π k²)`.

Proof. Write `Q(x, y)^{-s}` as the Gamma integral `(π^s/Γ(s)) ∫ t^{s-1} e^{-π Q t} dt`, exchange sum
and integral (`integral_tsum_of_summable_integral_norm`), Poisson-sum the Gaussian in `x` with the
shift `α = b y / 2` (`Complex.tsum_exp_neg_quadratic`, the Jacobi theta transformation) which
produces the phase `e^{2πikα} = (-1)^{kby}`, and exchange back. The `k = 0` term is the Gamma
integral `I(s; a, 0)`, the others are the `K`-Bessel-type integrals `I(s; a, πk²)`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Real

namespace CN1.CS

/-! ### Powers of positive reals with complex exponents -/

section Cpow

variable {x y : ℝ}

lemma cpow_pos_eq_exp (hx : 0 < x) (w : ℂ) : (x : ℂ) ^ w = cexp (w * (Real.log x : ℂ)) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le, mul_comm]

lemma cpow_inv_ofReal (hx : 0 < x) (w : ℂ) : ((x⁻¹ : ℝ) : ℂ) ^ w = (x : ℂ) ^ (-w) := by
  rw [cpow_pos_eq_exp (inv_pos.mpr hx), cpow_pos_eq_exp hx, Real.log_inv]
  congr 1
  push_cast
  ring

lemma cpow_mul_ofReal (hx : 0 < x) (hy : 0 < y) (w : ℂ) :
    ((x * y : ℝ) : ℂ) ^ w = (x : ℂ) ^ w * (y : ℂ) ^ w := by
  push_cast
  exact mul_cpow_ofReal_nonneg hx.le hy.le w

end Cpow

/-! ### The Jacobi theta transformation with a real shift -/

/-- `Σ_n e^{-π t (n + α)²} = t^{-1/2} Σ_k e^{-π k²/t} e^{2πikα}` for `t > 0`. -/
theorem theta_shift {t : ℝ} (ht : 0 < t) (α : ℝ) :
    ∑' n : ℤ, (Real.exp (-(π * t) * ((n : ℝ) + α) ^ 2) : ℂ) =
      (t : ℂ) ^ (-(1 / 2 : ℂ)) *
        ∑' k : ℤ, (Real.exp (-(π * (k : ℝ) ^ 2) / t) : ℂ) * cexp (2 * π * Complex.I * k * α) := by
  have ht' : 0 < (t : ℂ).re := by simpa using ht
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have h := Complex.tsum_exp_neg_quadratic ht' (-((t : ℂ) * α))
  have hC : cexp (π * t * α ^ 2) ≠ 0 := Complex.exp_ne_zero _
  have hL : ∀ n : ℤ, cexp (-π * (t : ℂ) * n ^ 2 + 2 * π * (-((t : ℂ) * α)) * n) =
      (Real.exp (-(π * t) * ((n : ℝ) + α) ^ 2) : ℂ) * cexp (π * t * α ^ 2) := by
    intro n
    rw [ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hR : ∀ n : ℤ, cexp (-π / (t : ℂ) * (n + Complex.I * (-((t : ℂ) * α))) ^ 2) =
      (Real.exp (-(π * (n : ℝ) ^ 2) / t) : ℂ) * cexp (2 * π * Complex.I * n * α) *
        cexp (π * t * α ^ 2) := by
    intro n
    rw [ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have hsq : ((n : ℂ) + Complex.I * (-((t : ℂ) * α))) ^ 2 =
        (n : ℂ) ^ 2 - 2 * Complex.I * t * α * n - (t : ℂ) ^ 2 * α ^ 2 := by
      linear_combination ((t : ℂ) ^ 2 * (α : ℂ) ^ 2) * Complex.I_sq
    rw [hsq]
    push_cast
    field_simp
    ring
  simp_rw [hL, hR] at h
  rw [tsum_mul_right, tsum_mul_right, ← mul_assoc, one_div, ← cpow_neg] at h
  exact mul_right_cancel₀ hC h

/-! ### The sign `(-1)^{k b y}` -/

/-- The sign `(-1)^{k b y}` (as a complex number). -/
noncomputable def sgn (d : ℕ) (k y : ℤ) : ℂ := (-1 : ℂ) ^ (k * (bq d : ℤ) * y)

lemma norm_sgn (d : ℕ) (k y : ℤ) : ‖sgn d k y‖ = 1 := by
  simp [sgn, norm_zpow]

lemma exp_eq_sgn (d : ℕ) (k y : ℤ) :
    cexp (2 * π * Complex.I * k * (((bq d : ℝ) * y / 2 : ℝ) : ℂ)) = sgn d k y := by
  have : (2 * π * Complex.I * k * (((bq d : ℝ) * y / 2 : ℝ) : ℂ)) =
      ((k * (bq d : ℤ) * y : ℤ) : ℂ) * (π * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I, sgn]

/-! ### The Gaussian slice -/

/-- `a_y = π d y² / 4`. -/
noncomputable def ay (d : ℕ) (y : ℤ) : ℝ := π * d * (y : ℝ) ^ 2 / 4

/-- `b_k = π k²`. -/
noncomputable def bk (k : ℤ) : ℝ := π * (k : ℝ) ^ 2

variable {d : ℕ}

lemma ay_pos (hd3 : 3 ≤ d) {y : ℤ} (hy : y ≠ 0) : 0 < ay d y := by
  unfold ay
  have : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  positivity

lemma bk_nonneg (k : ℤ) : 0 ≤ bk k := by unfold bk; positivity

lemma kern_Q_eq (hd : IsDisc d) (x y : ℤ) (t : ℝ) :
    kern (π * Q d x y) 0 t =
      (Real.exp (-(π * t) * ((x : ℝ) + (bq d : ℝ) * y / 2) ^ 2) : ℂ) *
        (Real.exp (-(ay d y * t)) : ℂ) := by
  rw [kern, ← ofReal_mul, ← Real.exp_add, Q_eq hd, ay]
  congr 2
  ring

/-- Poisson summation for the Gaussian slice: for `t > 0`,
`Σ_x e^{-π t Q(x,y)} = e^{-a_y t} t^{-1/2} Σ_k e^{-π k²/t} (-1)^{kby}`. -/
theorem tsum_kern_Q (hd : IsDisc d) {t : ℝ} (ht : 0 < t) (y : ℤ) :
    ∑' x : ℤ, kern (π * Q d x y) 0 t =
      (Real.exp (-(ay d y * t)) : ℂ) * ((t : ℂ) ^ (-(1 / 2 : ℂ)) *
        ∑' k : ℤ, (Real.exp (-(π * (k : ℝ) ^ 2) / t) : ℂ) * sgn d k y) := by
  simp_rw [kern_Q_eq hd]
  rw [tsum_mul_right, theta_shift ht, mul_comm]
  congr 2
  exact tsum_congr fun k => by rw [exp_eq_sgn]

/-! ### The Gamma integral for `q^{-s}` -/

lemma mellin_kern_zero {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    mellin (kern a 0) s = (1 / (a : ℂ)) ^ s * Gamma s := by
  rw [← integral_cpow_mul_exp_neg_mul_Ioi hs ha]
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  simp only [kern, smul_eq_mul, zero_div, add_zero, ofReal_exp, ofReal_neg, ofReal_mul]

/-- `q^{-s} = (π^s / Γ(s)) ∫₀^∞ t^{s-1} e^{-π q t} dt` for `q > 0`, `re s > 0`. -/
lemma cpow_neg_eq_mellin {q : ℝ} (hq : 0 < q) {s : ℂ} (hs : 0 < s.re) :
    (q : ℂ) ^ (-s) = (π : ℂ) ^ s / Gamma s * mellin (kern (π * q) 0) s := by
  rw [mellin_kern_zero (by positivity) hs]
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  have hπq : (0 : ℝ) < π * q := by positivity
  have e1 : (1 / ((π * q : ℝ) : ℂ)) ^ s = cexp (s * ((-Real.log π - Real.log q : ℝ) : ℂ)) := by
    rw [show (1 / ((π * q : ℝ) : ℂ)) = (((π * q)⁻¹ : ℝ) : ℂ) by push_cast; ring,
      cpow_pos_eq_exp (inv_pos.mpr hπq), Real.log_inv, Real.log_mul Real.pi_pos.ne' hq.ne']
    congr 1
    push_cast
    ring
  rw [e1, cpow_pos_eq_exp Real.pi_pos, cpow_pos_eq_exp hq]
  symm
  have h2 : cexp (s * (Real.log π : ℂ)) * cexp (s * ((-Real.log π - Real.log q : ℝ) : ℂ)) =
      cexp (-s * (Real.log q : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc cexp (s * (Real.log π : ℂ)) / Gamma s *
        (cexp (s * ((-Real.log π - Real.log q : ℝ) : ℂ)) * Gamma s)
      = (cexp (s * (Real.log π : ℂ)) * cexp (s * ((-Real.log π - Real.log q : ℝ) : ℂ))) *
          (Gamma s / Gamma s) := by ring
    _ = cexp (-s * (Real.log q : ℂ)) := by rw [div_self hG, mul_one, h2]

/-! ### Summability of `e^{-c|k|}` over `ℤ` -/

lemma summable_exp_neg_mul_abs_int {c : ℝ} (hc : 0 < c) :
    Summable fun k : ℤ => Real.exp (-(c * |(k : ℝ)|)) := by
  have hgeo : Summable fun n : ℕ => Real.exp (-c) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine hgeo.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    simp only [Int.cast_natCast, Nat.abs_cast]
    ring
  · refine hgeo.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
    ring

/-! ### The slice lemma -/

/-- **The Poisson slice lemma.** For `y ≠ 0` and `re s > 1`,
`Σ_x Q(x, y)^{-s} = (π^s / Γ(s)) Σ_k (-1)^{kby} I(s; a_y, b_k)`. -/
theorem slice (hd : IsDisc d) (h3 : 3 ≤ d) {s : ℂ} (hs : 1 < s.re) {y : ℤ} (hy : y ≠ 0) :
    ∑' x : ℤ, (Q d x y : ℂ) ^ (-s) =
      (π : ℂ) ^ s / Gamma s * ∑' k : ℤ, sgn d k y * I s (ay d y) (bk k) := by
  have hs0 : 0 < s.re := by linarith
  have hs2 : 1 / 2 < s.re := by linarith
  have hay : 0 < ay d y := ay_pos h3 hy
  have hQ : ∀ x : ℤ, 0 < Q d x y := fun x => Q_pos_of_ne_zero hd h3 hy
  -- Step 1: each term as a Gamma integral.
  have step1 : ∀ x : ℤ, (Q d x y : ℂ) ^ (-s) =
      (π : ℂ) ^ s / Gamma s * mellin (kern (π * Q d x y) 0) s :=
    fun x => cpow_neg_eq_mellin (hQ x) hs0
  simp_rw [step1]
  rw [tsum_mul_left]
  congr 1
  -- Step 2: exchange sum and integral in `x`.
  have hF_int : ∀ x : ℤ, Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * kern (π * Q d x y) 0 t)
      (volume.restrict (Ioi 0)) :=
    fun x => integrableOn_cpow_mul_kern (by have := hQ x; positivity) le_rfl hs0
  have hF_sum : Summable fun x : ℤ =>
      ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * kern (π * Q d x y) 0 t‖ := by
    have hsum := (summable_Q_rpow_slice hd h3 hs y).mul_left (Real.Gamma s.re * π⁻¹ ^ s.re)
    refine hsum.congr fun x => ?_
    have hx := hQ x
    have e : ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * kern (π * Q d x y) 0 t‖ =
        ∫ t : ℝ in Ioi 0, t ^ (s.re - 1) * Real.exp (-((π * Q d x y) * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp ht), sub_re, one_re,
        norm_kern, zero_div, add_zero]
    rw [e, Real.integral_rpow_mul_exp_neg_mul_Ioi hs0 (by positivity), one_div, mul_inv,
      Real.mul_rpow (inv_nonneg.mpr Real.pi_pos.le) (inv_nonneg.mpr hx.le),
      Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
    ring
  unfold mellin
  simp_rw [smul_eq_mul]
  rw [integral_tsum_of_summable_integral_norm hF_int hF_sum]
  -- Step 3: the `k`-side, as an integral of a sum.
  have hG_int : ∀ k : ℤ, Integrable
      (fun t : ℝ => sgn d k y * ((t : ℂ) ^ (s - 3 / 2) * kern (ay d y) (bk k) t))
      (volume.restrict (Ioi 0)) :=
    fun k => (integrableOn_I_integrand hay (bk_nonneg k) hs2).const_mul _
  have hG_sum : Summable fun k : ℤ =>
      ∫ t : ℝ in Ioi 0, ‖sgn d k y * ((t : ℂ) ^ (s - 3 / 2) * kern (ay d y) (bk k) t)‖ := by
    have hc : 0 < Real.sqrt (ay d y * π) := Real.sqrt_pos.mpr (by positivity)
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
      (fun k => ?_) ((summable_exp_neg_mul_abs_int hc).mul_left
        ((2 / ay d y) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2)))
    have hn : ∀ t : ℝ, ‖sgn d k y * ((t : ℂ) ^ (s - 3 / 2) * kern (ay d y) (bk k) t)‖ =
        ‖(t : ℂ) ^ (s - 3 / 2) * kern (ay d y) (bk k) t‖ := fun t => by
      rw [norm_mul, norm_sgn, one_mul]
    simp_rw [hn]
    refine (integral_norm_I_integrand_le hay (bk_nonneg k) hs2).trans (le_of_eq ?_)
    rw [bk, show ay d y * (π * (k : ℝ) ^ 2) = (ay d y * π) * (k : ℝ) ^ 2 by ring,
      Real.sqrt_mul (by positivity) ((k : ℝ) ^ 2), Real.sqrt_sq_eq_abs]
    ring
  simp_rw [I_eq_integral, ← integral_const_mul]
  rw [integral_tsum_of_summable_integral_norm hG_int hG_sum]
  -- Step 4: pointwise identity of the integrands, via the Poisson step.
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : 0 < t := mem_Ioi.mp ht
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  rw [tsum_mul_left, tsum_kern_Q hd ht y, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hT : (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-(1 / 2 : ℂ)) = (t : ℂ) ^ (s - 3 / 2) := by
    rw [← cpow_add _ _ ht0]
    congr 1
    ring
  have hk : kern (ay d y) (bk k) t =
      (Real.exp (-(ay d y * t)) : ℂ) * (Real.exp (-(π * (k : ℝ) ^ 2) / t) : ℂ) := by
    rw [kern, ← ofReal_mul, ← Real.exp_add, bk]
    congr 2
    ring
  rw [hk, ← hT]
  ring

end CN1.CS
