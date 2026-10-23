import Mathlib

/-!
# CN1.ChowlaSelberg.GammaIntegral: the integral `I(s; a, b)` and the AM–GM bound

`I(s; a, b) = ∫₀^∞ t^{s - 3/2} e^{-a t - b / t} dt`, defined as the Mellin transform of the
kernel `kern a b : t ↦ e^{-(a t + b / t)}` at `s - 1/2`. For `b = 0` it is the Gamma integral
`(1/a)^{s - 1/2} Γ(s - 1/2)`; in general it is a K-Bessel function, but we never name it so.

Main facts, for `a > 0`, `b ≥ 0`, `re s > 1/2`:
* `integrableOn_cpow_mul_kern`: the integrand is integrable on `(0, ∞)` (Mathlib's Mellin
  machinery, exponential decay at `∞`, boundedness at `0`);
* `norm_I_le`: `‖I(s; a, b)‖ ≤ e^{-√(ab)} (2/a)^{re s - 1/2} Γ(re s - 1/2)`, from
  `a t + b / t ≥ 2 √(ab)` (AM–GM) and the Gamma integral of `t^{re s - 3/2} e^{-(a/2) t}`;
* `differentiableAt_I`: holomorphy in `s` (`mellin_differentiableAt_of_isBigO_rpow_exp`);
* `I_ofReal`: `I(σ; a, b)` is real for real `σ`.
-/

open Complex Set MeasureTheory Filter Topology Asymptotics

namespace CN1.CS

/-- The kernel `t ↦ exp (-(a t + b / t))`, as a complex-valued function on `ℝ`. -/
noncomputable def kern (a b : ℝ) (t : ℝ) : ℂ := (Real.exp (-(a * t + b / t)) : ℂ)

/-- `I(s; a, b) = ∫₀^∞ t^{s - 3/2} e^{-a t - b/t} dt`, as the Mellin transform of `kern a b`
at `s - 1/2`. -/
noncomputable def I (s : ℂ) (a b : ℝ) : ℂ := mellin (kern a b) (s - 1 / 2)

variable {a b t σ : ℝ} {s : ℂ}

lemma norm_kern (a b t : ℝ) : ‖kern a b t‖ = Real.exp (-(a * t + b / t)) := by
  rw [kern, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma continuousOn_kern (a b : ℝ) : ContinuousOn (kern a b) (Ioi 0) := by
  unfold kern
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  refine Real.continuous_exp.comp_continuousOn ?_
  refine ContinuousOn.neg (ContinuousOn.add (by fun_prop) ?_)
  exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt ht)

/-- AM–GM: `2 √(ab) ≤ a t + b / t` for `t > 0`. -/
lemma two_sqrt_le (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) :
    2 * Real.sqrt (a * b) ≤ a * t + b / t := by
  have h1 : 0 ≤ a * t := by positivity
  have h2 : 0 ≤ b / t := by positivity
  have h := two_mul_le_add_sq (Real.sqrt (a * t)) (Real.sqrt (b / t))
  rw [Real.sq_sqrt h1, Real.sq_sqrt h2] at h
  have h3 : Real.sqrt (a * b) = Real.sqrt (a * t) * Real.sqrt (b / t) := by
    rw [← Real.sqrt_mul h1]
    congr 1
    field_simp
  rw [h3]; linarith

/-- The pointwise bound `e^{-(a t + b/t)} ≤ e^{-√(ab)} e^{-(a/2) t}` for `t > 0`. -/
lemma exp_kern_le (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) :
    Real.exp (-(a * t + b / t)) ≤ Real.exp (-Real.sqrt (a * b)) * Real.exp (-(a / 2 * t)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := two_sqrt_le ha hb ht
  have h2 : 0 ≤ b / t := by positivity
  linarith

lemma kern_isBigO_atTop (ha : 0 < a) (hb : 0 ≤ b) :
    kern a b =O[atTop] fun t => Real.exp (-a * t) := by
  refine IsBigO.of_bound' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_kern, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have : 0 ≤ b / t := by positivity
  linarith

lemma kern_isBigO_zero (ha : 0 ≤ a) (hb : 0 ≤ b) :
    kern a b =O[𝓝[>] 0] fun t : ℝ => t ^ (-(0 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [norm_kern, neg_zero, Real.rpow_zero, norm_one, one_mul]
  have : 0 ≤ a * t + b / t := by
    have := le_of_lt (mem_Ioi.mp ht); positivity
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- The Mellin integral of the kernel converges for `re s > 0`. -/
lemma mellinConvergent_kern (ha : 0 < a) (hb : 0 ≤ b) (hs : 0 < s.re) :
    MellinConvergent (kern a b) s :=
  mellinConvergent_of_isBigO_rpow_exp ha
    ((continuousOn_kern a b).locallyIntegrableOn measurableSet_Ioi)
    (kern_isBigO_atTop ha hb) (kern_isBigO_zero ha.le hb) hs

lemma integrableOn_cpow_mul_kern (ha : 0 < a) (hb : 0 ≤ b) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * kern a b t) (Ioi 0) := by
  have h := mellinConvergent_kern ha hb hs
  simpa only [MellinConvergent, smul_eq_mul] using h

/-- Integrability of the real Gamma-type integrand `t^{σ - 1} e^{-r t}` on `(0, ∞)`. -/
lemma integrableOn_rpow_mul_exp {r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((σ : ℂ) - 1) * kern r 0 t‖) (Ioi 0) :=
    (integrableOn_cpow_mul_kern (s := (σ : ℂ)) hr le_rfl (by simpa using hσ)).norm
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioi
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp ht), sub_re, ofReal_re,
    one_re, norm_kern, zero_div, add_zero]

lemma I_eq_integral (s : ℂ) (a b : ℝ) :
    I s a b = ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 3 / 2) * kern a b t := by
  have h : s - 1 / 2 - 1 = s - 3 / 2 := by ring
  simp only [I, mellin, h, smul_eq_mul]

/-- The integrand of `I` is integrable for `re s > 1/2`. -/
lemma integrableOn_I_integrand (ha : 0 < a) (hb : 0 ≤ b) (hs : 1 / 2 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 3 / 2) * kern a b t) (Ioi 0) := by
  have h := integrableOn_cpow_mul_kern (s := s - 1 / 2) ha hb (by simp; linarith)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  congr 2
  ring

/-- The `b = 0` case is the Gamma integral: `I(s; a, 0) = (1/a)^{s - 1/2} Γ(s - 1/2)`. -/
lemma I_zero (ha : 0 < a) (hs : 1 / 2 < s.re) :
    I s a 0 = (1 / (a : ℂ)) ^ (s - 1 / 2) * Gamma (s - 1 / 2) := by
  have hs' : 0 < (s - 1 / 2).re := by simp; linarith
  rw [← integral_cpow_mul_exp_neg_mul_Ioi hs' ha]
  unfold I mellin
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  simp only [kern, smul_eq_mul, zero_div, add_zero, ofReal_exp, ofReal_neg, ofReal_mul]

/-- The real majorant integral: `∫₀^∞ t^{σ - 3/2} e^{-(a/2) t} dt = (2/a)^{σ - 1/2} Γ(σ - 1/2)`. -/
lemma integral_majorant (ha : 0 < a) (hσ : 1 / 2 < σ) :
    ∫ t in Ioi 0, t ^ (σ - 1 / 2 - 1) * Real.exp (-(a / 2 * t)) =
      (2 / a) ^ (σ - 1 / 2) * Real.Gamma (σ - 1 / 2) := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)]
  congr 2
  field_simp

/-- **The key bound** on the integral of the norm of the integrand of `I(s; a, b)`:
`∫₀^∞ ‖t^{s - 3/2} e^{-a t - b/t}‖ dt ≤ e^{-√(ab)} (2/a)^{re s - 1/2} Γ(re s - 1/2)`. -/
theorem integral_norm_I_integrand_le (ha : 0 < a) (hb : 0 ≤ b) (hs : 1 / 2 < s.re) :
    ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 3 / 2) * kern a b t‖ ≤
      Real.exp (-Real.sqrt (a * b)) * ((2 / a) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2)) := by
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-Real.sqrt (a * b)) *
      (t ^ (s.re - 1 / 2 - 1) * Real.exp (-(a / 2 * t)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp (by linarith) (by positivity)).const_mul _
  calc ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 3 / 2) * kern a b t‖
      ≤ ∫ t in Ioi 0, Real.exp (-Real.sqrt (a * b)) *
          (t ^ (s.re - 1 / 2 - 1) * Real.exp (-(a / 2 * t))) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) hint ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht' : 0 < t := mem_Ioi.mp ht
        have hre : (s - 3 / 2).re = s.re - 1 / 2 - 1 := by simp; ring
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht', norm_kern, hre]
        calc t ^ (s.re - 1 / 2 - 1) * Real.exp (-(a * t + b / t))
            ≤ t ^ (s.re - 1 / 2 - 1) * (Real.exp (-Real.sqrt (a * b)) * Real.exp (-(a / 2 * t))) :=
              mul_le_mul_of_nonneg_left (exp_kern_le ha.le hb ht') (Real.rpow_nonneg ht'.le _)
          _ = _ := by ring
    _ = Real.exp (-Real.sqrt (a * b)) * ((2 / a) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2)) := by
        rw [integral_const_mul, integral_majorant ha hs]

/-- `‖I(s; a, b)‖ ≤ e^{-√(ab)} (2/a)^{re s - 1/2} Γ(re s - 1/2)` for `re s > 1/2`. -/
theorem norm_I_le (ha : 0 < a) (hb : 0 ≤ b) (hs : 1 / 2 < s.re) :
    ‖I s a b‖ ≤
      Real.exp (-Real.sqrt (a * b)) * ((2 / a) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2)) := by
  rw [I_eq_integral]
  exact (norm_integral_le_integral_norm _).trans (integral_norm_I_integrand_le ha hb hs)

/-- `I(·; a, b)` is holomorphic on `re s > 1/2`. -/
theorem differentiableAt_I (ha : 0 < a) (hb : 0 ≤ b) (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun s => I s a b) s := by
  have h1 : DifferentiableAt ℂ (mellin (kern a b)) (s - 1 / 2) :=
    mellin_differentiableAt_of_isBigO_rpow_exp ha
      ((continuousOn_kern a b).locallyIntegrableOn measurableSet_Ioi)
      (kern_isBigO_atTop ha hb) (kern_isBigO_zero ha.le hb) (by simp; linarith)
  exact h1.comp s (differentiableAt_id.sub_const _)

/-- `I(σ; a, b)` is the real integral `∫₀^∞ t^{σ - 3/2} e^{-a t - b/t} dt` for real `σ`. -/
theorem I_ofReal (σ a b : ℝ) :
    I (σ : ℂ) a b =
      ((∫ t in Ioi 0, t ^ (σ - 3 / 2) * Real.exp (-(a * t + b / t)) : ℝ) : ℂ) := by
  rw [I_eq_integral, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp only [kern, ofReal_mul]
  congr 1
  rw [Complex.ofReal_cpow (le_of_lt (mem_Ioi.mp ht))]
  push_cast
  ring_nf

theorem I_ofReal_im (σ a b : ℝ) : (I (σ : ℂ) a b).im = 0 := by
  rw [I_ofReal, ofReal_im]

end CN1.CS
