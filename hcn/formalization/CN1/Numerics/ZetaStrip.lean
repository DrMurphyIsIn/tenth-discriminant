import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.PSeriesComplex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected

/-!
# `riemannZeta` on the half-plane `0 < re s` as an explicit series

Pinned environment: Lean v4.34.1, Mathlib d13f23b (the openai/math `OAI` root). Mathlib only.

Mathlib evaluates `riemannZeta s` as a Dirichlet series only for `1 < re s`. The argument needs the
values `ζ(3/4)` and `ζ(7/8)`, which lie in the critical strip, so we need a representation valid on
`0 < re s` that is *about Mathlib's `riemannZeta`* (so that the trust base stays Mathlib's). This
file proves the
first-order Euler–Maclaurin representation in a form whose remainder is an explicit series:

* `w a s = s (a^{1-s} - (a+1)^{1-s}) - (s-1) a (a^{-s} - (a+1)^{-s})`, which is entire in `s` and
  equals `s (s-1) ∫_a^{a+1} (x - a) x^{-s-1} dx`, hence `‖w a s‖ ≤ ‖s‖ ‖s-1‖ a^{-re s - 1}`;
* `W s = ∑_{n ≥ 0} w (n+1) s`, differentiable on `0 < re s`;
* `riemannZeta₁ s = s - W s` on `0 < re s`, where Mathlib's `riemannZeta₁ s = (s-1) ζ(s)` is entire.

The last identity is proved on `1 < re s` by telescoping the partial sums and then carried over by
the identity theorem on the convex half-plane `{0 < re s}`; because `riemannZeta₁` is entire no
punctured domain is needed. Consequently, for `0 < re s`, `s ≠ 1`,
`riemannZeta s = (s - 1)⁻¹ * (s - W s)`.

The real-variable evaluation with an explicit remainder bound is in `ZetaReal.lean`.
-/

set_option autoImplicit false

namespace CN1.Numerics

open Complex Filter Topology Set intervalIntegral
open scoped Interval

/-- The building block of the series: `s (a^{1-s} - (a+1)^{1-s}) - (s-1) a (a^{-s} - (a+1)^{-s})`.
It equals `s (s-1) ∫_a^{a+1} (x - a) x^{-s-1} dx` (`w_eq_integral`). -/
noncomputable def w (a : ℝ) (s : ℂ) : ℂ :=
  s * ((a : ℂ) ^ (1 - s) - ((a : ℂ) + 1) ^ (1 - s))
    - (s - 1) * a * ((a : ℂ) ^ (-s) - ((a : ℂ) + 1) ^ (-s))

/-- The remainder series `∑_{n ≥ 0} w (n+1) s`. -/
noncomputable def W (s : ℂ) : ℂ := ∑' n : ℕ, w ((n : ℝ) + 1) s

lemma zero_notMem_uIcc {a : ℝ} (ha : 0 < a) : (0 : ℝ) ∉ [[a, a + 1]] := by
  rw [Set.uIcc_of_le (by linarith)]
  rintro ⟨h, -⟩
  linarith

lemma sub_one_mul_integral_cpow_neg {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (s - 1) * ∫ x in a..(a + 1), (x : ℂ) ^ (-s) = (a : ℂ) ^ (1 - s) - ((a : ℂ) + 1) ^ (1 - s) := by
  by_cases hs : s = 1
  · subst hs; simp
  · have h1 : (-s : ℂ) ≠ -1 := fun h => hs (neg_injective h)
    rw [integral_cpow (Or.inr ⟨h1, zero_notMem_uIcc ha⟩)]
    push_cast
    rw [show (-s + 1 : ℂ) = 1 - s by ring]
    have h2 : (1 - s : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    rw [mul_div_assoc', div_eq_iff h2]
    ring

lemma mul_integral_cpow_neg_sub_one {a : ℝ} (ha : 0 < a) (s : ℂ) :
    s * ∫ x in a..(a + 1), (x : ℂ) ^ (-s - 1) = (a : ℂ) ^ (-s) - ((a : ℂ) + 1) ^ (-s) := by
  by_cases hs : s = 0
  · subst hs; simp
  · have h1 : (-s - 1 : ℂ) ≠ -1 := by
      intro h; apply hs; linear_combination -h
    rw [integral_cpow (Or.inr ⟨h1, zero_notMem_uIcc ha⟩)]
    push_cast
    rw [show (-s - 1 + 1 : ℂ) = -s by ring]
    have h2 : (-s : ℂ) ≠ 0 := neg_ne_zero.mpr hs
    rw [mul_div_assoc', div_eq_iff h2]
    ring

/-- `w a s = s (s-1) ∫_a^{a+1} (x - a) x^{-s-1} dx`. -/
lemma w_eq_integral {a : ℝ} (ha : 0 < a) (s : ℂ) :
    w a s = s * (s - 1) * ∫ x in a..(a + 1), ((x : ℂ) - a) * (x : ℂ) ^ (-s - 1) := by
  have h0 := zero_notMem_uIcc ha
  have hi1 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) MeasureTheory.volume a (a + 1) :=
    intervalIntegrable_cpow (Or.inr h0)
  have hi2 : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) MeasureTheory.volume a (a + 1) :=
    intervalIntegrable_cpow (Or.inr h0)
  have key : (∫ x in a..(a + 1), ((x : ℂ) - a) * (x : ℂ) ^ (-s - 1))
      = (∫ x in a..(a + 1), (x : ℂ) ^ (-s)) - a * ∫ x in a..(a + 1), (x : ℂ) ^ (-s - 1) := by
    rw [← integral_const_mul, ← integral_sub hi1 (hi2.const_mul _)]
    refine integral_congr fun x hx => ?_
    have hx0 : (x : ℂ) ≠ 0 := by
      have : x ≠ 0 := ne_of_mem_of_not_mem hx h0
      exact_mod_cast this
    have e : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * (x : ℂ) := by
      conv_lhs => rw [show (-s : ℂ) = (-s - 1) + 1 by ring]
      rw [cpow_add _ _ hx0, cpow_one]
    rw [e]
    ring
  rw [key, w, ← sub_one_mul_integral_cpow_neg ha, ← mul_integral_cpow_neg_sub_one ha]
  ring

/-- The bound `‖w a s‖ ≤ ‖s‖ ‖s-1‖ a^{-(re s + 1)}`, for `-1 < re s`. -/
lemma norm_w_le {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : -1 < s.re) :
    ‖w a s‖ ≤ ‖s‖ * ‖s - 1‖ * a ^ (-(s.re + 1)) := by
  rw [w_eq_integral ha, norm_mul, norm_mul]
  gcongr
  have hb : ∀ x ∈ Ι a (a + 1),
      ‖((x : ℂ) - a) * (x : ℂ) ^ (-s - 1)‖ ≤ a ^ (-(s.re + 1)) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : 0 < x := by linarith
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0]
    have e1 : ‖(x : ℂ) - a‖ = x - a := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have e2 : (-s - 1).re = -(s.re + 1) := by
      rw [Complex.sub_re, Complex.neg_re, Complex.one_re]; ring
    rw [e1, e2]
    calc (x - a) * x ^ (-(s.re + 1)) ≤ 1 * a ^ (-(s.re + 1)) := by
          apply mul_le_mul (by linarith) _ (Real.rpow_nonneg hx0.le _) zero_le_one
          exact (Real.rpow_le_rpow_iff_of_neg hx0 ha (by linarith)).mpr hx1.le
      _ = a ^ (-(s.re + 1)) := one_mul _
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

lemma differentiable_w {a : ℝ} (ha : 0 < a) : Differentiable ℂ (w a) := by
  have h1 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h2 : (a : ℂ) + 1 ≠ 0 := by
    have : (0 : ℝ) < a + 1 := by linarith
    exact_mod_cast this.ne'
  have d1 : Differentiable ℂ fun s : ℂ => (a : ℂ) ^ (1 - s) :=
    Differentiable.const_cpow ((differentiable_const _).sub differentiable_id) (Or.inl h1)
  have d2 : Differentiable ℂ fun s : ℂ => ((a : ℂ) + 1) ^ (1 - s) :=
    Differentiable.const_cpow ((differentiable_const _).sub differentiable_id) (Or.inl h2)
  have d3 : Differentiable ℂ fun s : ℂ => (a : ℂ) ^ (-s) :=
    Differentiable.const_cpow differentiable_id.neg (Or.inl h1)
  have d4 : Differentiable ℂ fun s : ℂ => ((a : ℂ) + 1) ^ (-s) :=
    Differentiable.const_cpow differentiable_id.neg (Or.inl h2)
  unfold w
  exact (differentiable_id.mul (d1.sub d2)).sub
    (((differentiable_id.sub_const _).mul_const _).mul (d3.sub d4))

/-- Telescoped partial sums. -/
lemma sum_w (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, w ((n : ℝ) + 1) s
      = s * (1 - ((N : ℂ) + 1) ^ (1 - s))
        - (s - 1) * ((∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-s)) - N * ((N : ℂ) + 1) ^ (-s)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    unfold w
    push_cast
    ring

lemma summable_rpow_add_one (p : ℝ) (hp : p < -1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ p := by
  have := (Real.summable_nat_rpow (p := p)).mpr hp
  have h := (summable_nat_add_iff 1).mpr this
  simpa using h

lemma summable_w {s : ℂ} (hs : 0 < s.re) : Summable fun n : ℕ => w ((n : ℝ) + 1) s := by
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => ‖s‖ * ‖s - 1‖ * ((n : ℝ) + 1) ^ (-(s.re + 1))) ?_ ?_
  · exact (summable_rpow_add_one _ (by linarith)).mul_left _
  · intro n
    exact norm_w_le (by positivity) (by linarith)

/-- On `1 < re s` the series sums to `s - (s-1) ζ(s)`. -/
lemma hasSum_w {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => w ((n : ℝ) + 1) s) (s - (s - 1) * riemannZeta s) := by
  have hs0 : 0 < s.re := by linarith
  rw [(summable_w hs0).hasSum_iff_tendsto_nat]
  simp_rw [sum_w]
  have hpos : ∀ N : ℕ, (0 : ℝ) < (N : ℝ) + 1 := fun N => by positivity
  have hcast : ∀ N : ℕ, ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := fun N => by norm_cast
  have hlim : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-(s.re - 1))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have l1 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ N : ℕ, ‖((N : ℂ) + 1) ^ (1 - s)‖ = ((N : ℝ) + 1) ^ (-(s.re - 1)) := by
      intro N
      rw [hcast N, norm_cpow_eq_rpow_re_of_pos (hpos N)]
      congr 1
      rw [Complex.sub_re, Complex.one_re]; ring
    simp_rw [e]
    exact hlim
  have l2 : Tendsto (fun N : ℕ => (N : ℂ) * ((N : ℂ) + 1) ^ (-s)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun N : ℕ => ((N : ℝ) + 1) ^ (-(s.re - 1))) ?_ hlim
    intro N
    rw [norm_mul, hcast N, norm_cpow_eq_rpow_re_of_pos (hpos N), Complex.neg_re,
      Complex.norm_natCast]
    have : ((N : ℝ) + 1) ^ (-(s.re - 1)) = ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (-s.re) := by
      rw [show -(s.re - 1) = -s.re + 1 by ring, Real.rpow_add_one (hpos N).ne']; ring
    rw [this]
    gcongr
    linarith
  have l3 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-s)) atTop
      (𝓝 (riemannZeta s)) := by
    have hsum : Summable fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s := by
      have := (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
      have h := (summable_nat_add_iff 1).mpr this
      simpa using h
    have h2 := hsum.hasSum.tendsto_sum_nat
    rw [← zeta_eq_tsum_one_div_nat_add_one_cpow hs] at h2
    refine h2.congr fun N => Finset.sum_congr rfl fun n _ => ?_
    rw [cpow_neg, one_div]
  have := ((tendsto_const_nhds (x := s)).mul ((tendsto_const_nhds (x := (1 : ℂ))).sub l1)).sub
    ((tendsto_const_nhds (x := s - 1)).mul (l3.sub l2))
  convert this using 2
  ring

lemma riemannZeta₁_eq_mul {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hs), one_mul]

/-- `W` is differentiable on the half-plane `0 < re s`. -/
lemma differentiableOn_W : DifferentiableOn ℂ W {z : ℂ | 0 < z.re} := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hz' : 0 < z.re := hz
  set ε := z.re / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hball : DifferentiableOn ℂ W (Metric.ball z ε) := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ => (‖z‖ + ε) * (‖z‖ + ε + 1) * ((n : ℝ) + 1) ^ (-(ε + 1))) ?_ ?_
      Metric.isOpen_ball ?_
    · exact (summable_rpow_add_one _ (by linarith)).mul_left _
    · intro n
      exact (differentiable_w (by positivity)).differentiableOn
    · intro n x hx
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have hre : ε < x.re := by
        have h1 := Complex.abs_re_le_norm (x - z)
        rw [Complex.sub_re] at h1
        have h2 := (abs_le.mp h1).1
        linarith
      have hre' : -1 < x.re := by linarith
      have hx1 : ‖x‖ ≤ ‖z‖ + ε := by
        have := norm_sub_norm_le x z
        linarith
      have hx2 : ‖x - 1‖ ≤ ‖z‖ + ε + 1 := by
        have := norm_sub_le x 1
        rw [norm_one] at this
        linarith
      have hx3 : ((n : ℝ) + 1) ^ (-(x.re + 1)) ≤ ((n : ℝ) + 1) ^ (-(ε + 1)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by linarith)
      calc ‖w ((n : ℝ) + 1) x‖ ≤ ‖x‖ * ‖x - 1‖ * ((n : ℝ) + 1) ^ (-(x.re + 1)) :=
            norm_w_le (by positivity) hre'
        _ ≤ (‖z‖ + ε) * (‖z‖ + ε + 1) * ((n : ℝ) + 1) ^ (-(ε + 1)) := by gcongr
  exact hball.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε0))

/-- **The representation.** On `0 < re s`, `riemannZeta₁ s = s - W s`, where Mathlib's
`riemannZeta₁ s = (s - 1) * riemannZeta s` for `s ≠ 1`. -/
theorem riemannZeta₁_eq_sub_W {s : ℂ} (hs : 0 < s.re) : riemannZeta₁ s = s - W s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUc : Convex ℝ {z : ℂ | 0 < z.re} := convex_halfSpace_re_gt 0
  have hf : AnalyticOnNhd ℂ riemannZeta₁ {z : ℂ | 0 < z.re} :=
    (analyticOnNhd_iff_differentiableOn hU).mpr differentiable_riemannZeta₁.differentiableOn
  have hg : AnalyticOnNhd ℂ (fun z => z - W z) {z : ℂ | 0 < z.re} :=
    (analyticOnNhd_iff_differentiableOn hU).mpr (differentiableOn_id.sub differentiableOn_W)
  have h2 : (2 : ℂ) ∈ {z : ℂ | 0 < z.re} := by simp
  have hfg : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] fun z => z - W z := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by simp
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz : 1 < z.re := hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      simp at hz
    show riemannZeta₁ z = z - W z
    rw [W, (hasSum_w hz).tsum_eq, riemannZeta₁_eq_mul hz1]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc.isPreconnected h2 hfg hs

/-- For `0 < re s`, `s ≠ 1`: `riemannZeta s = (s - 1)⁻¹ * (s - W s)`. -/
theorem riemannZeta_eq_of_pos_re {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = (s - 1)⁻¹ * (s - W s) := by
  rw [riemannZeta_eq_inv_sub_mul hs1, riemannZeta₁_eq_sub_W hs]

end CN1.Numerics
