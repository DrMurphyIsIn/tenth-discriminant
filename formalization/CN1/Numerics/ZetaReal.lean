import CN1.Numerics.ZetaStrip
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Euler–Maclaurin for `riemannZeta` at real points, with an explicit remainder

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib only.

From `ZetaStrip.lean`: for `0 < re s`, `s ≠ 1`, `riemannZeta s = (s-1)⁻¹ (s - W s)` with
`W s = ∑_{n≥0} w (n+1) s`. Here we specialise to real `σ > 0`, `σ ≠ 1`, where everything is real:

* `wR a σ` is the real value of `w a σ`, and `W σ = WR σ` (`W_ofReal`);
* `wR a σ = (σ-1)(a^{-σ} - (a+1)^{-σ})/2 + σ(σ-1) vR a σ`, where
  `vR a σ = ∫_a^{a+1} x^{-σ-1} (x - a - 1/2) dx` satisfies `-(σ+1) a^{-σ-2}/8 ≤ vR a σ ≤ 0`
  (integration by parts against `P(x) = (x-a)(x-a-1)/2 ∈ [-1/8, 0]`);
* telescoping the finite part and summing the tail gives the **Euler–Maclaurin formula**
  (`riemannZeta_ofReal_eulerMaclaurin`): for `M : ℕ`, `N = M + 1`,

    `ζ(σ) = ∑_{n=1}^{M} n^{-σ} + N^{1-σ}/(σ-1) + N^{-σ}/2 + R`,   `0 ≤ R ≤ σ (σ+2)/8 · N^{-σ-1}`.

Everything is stated about Mathlib's `riemannZeta`. The statement also shows that
`riemannZeta σ` is real for real `σ > 0`, `σ ≠ 1`.
-/

set_option autoImplicit false

namespace CN1.Numerics

open Real Filter Topology Set intervalIntegral
open scoped Interval

/-- The real value of `w a σ`. -/
noncomputable def wR (a σ : ℝ) : ℝ :=
  σ * (a ^ (1 - σ) - (a + 1) ^ (1 - σ)) - (σ - 1) * a * (a ^ (-σ) - (a + 1) ^ (-σ))

/-- The real value of `W σ`. -/
noncomputable def WR (σ : ℝ) : ℝ := ∑' n : ℕ, wR ((n : ℝ) + 1) σ

lemma w_ofReal {a : ℝ} (ha : 0 < a) (σ : ℝ) : w a σ = (wR a σ : ℂ) := by
  have ha1 : (0 : ℝ) ≤ a + 1 := by linarith
  simp only [w, wR, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_neg,
    Complex.ofReal_cpow ha.le, Complex.ofReal_cpow ha1, Complex.ofReal_add]

lemma W_ofReal (σ : ℝ) : W σ = (WR σ : ℂ) := by
  unfold W WR
  rw [Complex.ofReal_tsum]
  congr 1
  ext n
  rw [w_ofReal (by positivity)]

lemma summable_wR {σ : ℝ} (hσ : 0 < σ) : Summable fun n : ℕ => wR ((n : ℝ) + 1) σ := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  have h := summable_w hs
  simp_rw [w_ofReal (by positivity : (0 : ℝ) < (_ : ℕ) + 1)] at h
  exact Complex.summable_ofReal.mp h

/-- `riemannZeta σ = (σ-1)⁻¹ (σ - WR σ)` for real `σ > 0`, `σ ≠ 1`; in particular it is real. -/
theorem riemannZeta_ofReal_eq {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    riemannZeta σ = (((σ - 1)⁻¹ * (σ - WR σ) : ℝ) : ℂ) := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1
  rw [riemannZeta_eq_of_pos_re hs hs1, W_ofReal]
  push_cast
  ring

/-! ### Real integral identities -/

lemma sub_one_mul_integral_rpow_neg {a : ℝ} (ha : 0 < a) (σ : ℝ) :
    (σ - 1) * ∫ x in a..(a + 1), x ^ (-σ) = a ^ (1 - σ) - (a + 1) ^ (1 - σ) := by
  by_cases hs : σ = 1
  · subst hs; simp
  · have h1 : -σ ≠ -1 := fun h => hs (neg_injective h)
    rw [integral_rpow (Or.inr ⟨h1, zero_notMem_uIcc ha⟩)]
    rw [show -σ + 1 = 1 - σ by ring]
    have h2 : 1 - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
    rw [mul_div_assoc', div_eq_iff h2]
    ring

lemma mul_integral_rpow_neg_sub_one {a : ℝ} (ha : 0 < a) (σ : ℝ) :
    σ * ∫ x in a..(a + 1), x ^ (-σ - 1) = a ^ (-σ) - (a + 1) ^ (-σ) := by
  by_cases hs : σ = 0
  · subst hs; simp
  · have h1 : -σ - 1 ≠ -1 := by
      intro h; apply hs; linarith
    rw [integral_rpow (Or.inr ⟨h1, zero_notMem_uIcc ha⟩)]
    rw [show -σ - 1 + 1 = -σ by ring]
    have h2 : -σ ≠ 0 := neg_ne_zero.mpr hs
    rw [mul_div_assoc', div_eq_iff h2]
    ring

/-- The midpoint-corrected integral `∫_a^{a+1} x^{-σ-1} (x - a - 1/2) dx`. -/
noncomputable def vR (a σ : ℝ) : ℝ := ∫ x in a..(a + 1), x ^ (-σ - 1) * (x - a - 1 / 2)

lemma wR_eq_vR {a : ℝ} (ha : 0 < a) (σ : ℝ) :
    wR a σ = (σ - 1) * (a ^ (-σ) - (a + 1) ^ (-σ)) / 2 + σ * (σ - 1) * vR a σ := by
  have h0 := zero_notMem_uIcc ha
  have hi1 : IntervalIntegrable (fun x : ℝ => x ^ (-σ)) MeasureTheory.volume a (a + 1) :=
    intervalIntegrable_rpow (Or.inr h0)
  have hi2 : IntervalIntegrable (fun x : ℝ => x ^ (-σ - 1)) MeasureTheory.volume a (a + 1) :=
    intervalIntegrable_rpow (Or.inr h0)
  have hi3 : IntervalIntegrable (fun x : ℝ => x ^ (-σ - 1) * (x - a - 1 / 2))
      MeasureTheory.volume a (a + 1) :=
    hi2.mul_continuousOn (by fun_prop)
  -- `∫ x^{-σ} - a ∫ x^{-σ-1} = vR + (1/2) ∫ x^{-σ-1}`
  have key : (∫ x in a..(a + 1), x ^ (-σ)) - a * ∫ x in a..(a + 1), x ^ (-σ - 1)
      = vR a σ + (1 / 2) * ∫ x in a..(a + 1), x ^ (-σ - 1) := by
    rw [vR, ← integral_const_mul, ← integral_const_mul, ← integral_sub hi1 (hi2.const_mul _),
      ← integral_add hi3 (hi2.const_mul _)]
    refine integral_congr fun x hx => ?_
    have hx0 : x ≠ 0 := ne_of_mem_of_not_mem hx h0
    have e : x ^ (-σ) = x ^ (-σ - 1) * x := by
      conv_lhs => rw [show -σ = (-σ - 1) + 1 by ring]
      rw [Real.rpow_add_one hx0]
    rw [e]
    ring
  have hw : wR a σ = σ * (σ - 1) *
      ((∫ x in a..(a + 1), x ^ (-σ)) - a * ∫ x in a..(a + 1), x ^ (-σ - 1)) := by
    rw [wR, ← sub_one_mul_integral_rpow_neg ha, ← mul_integral_rpow_neg_sub_one ha]
    ring
  rw [hw, key, mul_add, ← mul_assoc, show σ * (σ - 1) * (1 / 2) * ∫ x in a..(a + 1), x ^ (-σ - 1)
      = (σ - 1) / 2 * (σ * ∫ x in a..(a + 1), x ^ (-σ - 1)) by ring,
    mul_integral_rpow_neg_sub_one ha]
  ring

/-- `-(σ+1) a^{-σ-2}/8 ≤ vR a σ ≤ 0`, by integration by parts. -/
lemma vR_bounds {a : ℝ} (ha : 0 < a) {σ : ℝ} (hσ : 0 < σ) :
    -((σ + 1) * a ^ (-σ - 2) / 8) ≤ vR a σ ∧ vR a σ ≤ 0 := by
  have h0 := zero_notMem_uIcc ha
  have hab : a ≤ a + 1 := by linarith
  -- integration by parts with u = x^{-σ-1}, v = (x-a)(x-(a+1))/2
  have hu : ∀ x ∈ [[a, a + 1]], HasDerivAt (fun x : ℝ => x ^ (-σ - 1))
      ((-σ - 1) * x ^ (-σ - 2)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_mem_of_not_mem hx h0
    have := Real.hasDerivAt_rpow_const (p := -σ - 1) (Or.inl hx0)
    rwa [show -σ - 1 - 1 = -σ - 2 by ring] at this
  have hv : ∀ x ∈ [[a, a + 1]], HasDerivAt (fun x : ℝ => (x - a) * (x - (a + 1)) / 2)
      (x - a - 1 / 2) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => (x - a) * (x - (a + 1)))
        (1 * (x - (a + 1)) + (x - a) * 1) x :=
      ((hasDerivAt_id x).sub_const a).mul ((hasDerivAt_id x).sub_const (a + 1))
    exact (h1.div_const 2).congr_deriv (by ring)
  have hu' : IntervalIntegrable (fun x : ℝ => (-σ - 1) * x ^ (-σ - 2)) MeasureTheory.volume a (a + 1) :=
    (intervalIntegrable_rpow (Or.inr h0)).const_mul _
  have hv' : IntervalIntegrable (fun x : ℝ => x - a - 1 / 2) MeasureTheory.volume a (a + 1) :=
    (by fun_prop : Continuous fun x : ℝ => x - a - 1 / 2).intervalIntegrable _ _
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hI : vR a σ = -∫ x in a..(a + 1), (-σ - 1) * x ^ (-σ - 2) * ((x - a) * (x - (a + 1)) / 2) := by
    rw [vR, ibp]
    simp
  -- bounds on the remaining integrand
  have hint : IntervalIntegrable (fun x : ℝ => (-σ - 1) * x ^ (-σ - 2) * ((x - a) * (x - (a + 1)) / 2))
      MeasureTheory.volume a (a + 1) :=
    hu'.mul_continuousOn (by fun_prop)
  have hpt : ∀ x ∈ Icc a (a + 1),
      0 ≤ (-σ - 1) * x ^ (-σ - 2) * ((x - a) * (x - (a + 1)) / 2) ∧
      (-σ - 1) * x ^ (-σ - 2) * ((x - a) * (x - (a + 1)) / 2) ≤ (σ + 1) * a ^ (-σ - 2) / 8 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx0 : 0 < x := by linarith
    have hq : 0 < x ^ (-σ - 2) := Real.rpow_pos_of_pos hx0 _
    have hqa : x ^ (-σ - 2) ≤ a ^ (-σ - 2) :=
      (Real.rpow_le_rpow_iff_of_neg hx0 ha (by linarith)).mpr hx1
    have hP0 : 0 ≤ -((x - a) * (x - (a + 1)) / 2) := by nlinarith
    have hP1 : -((x - a) * (x - (a + 1)) / 2) ≤ 1 / 8 := by nlinarith [sq_nonneg (x - a - 1 / 2)]
    have e : (-σ - 1) * x ^ (-σ - 2) * ((x - a) * (x - (a + 1)) / 2)
        = (σ + 1) * x ^ (-σ - 2) * (-((x - a) * (x - (a + 1)) / 2)) := by ring
    rw [e]
    constructor
    · exact mul_nonneg (mul_nonneg (by linarith) hq.le) hP0
    · calc (σ + 1) * x ^ (-σ - 2) * (-((x - a) * (x - (a + 1)) / 2))
          ≤ (σ + 1) * a ^ (-σ - 2) * (1 / 8) := by
            apply mul_le_mul _ hP1 hP0 (by positivity)
            exact mul_le_mul_of_nonneg_left hqa (by linarith)
        _ = (σ + 1) * a ^ (-σ - 2) / 8 := by ring
  have hlo : (0 : ℝ) ≤ ∫ x in a..(a + 1), (-σ - 1) * x ^ (-σ - 2) * ((x - a) * (x - (a + 1)) / 2) := by
    have := intervalIntegral.integral_mono_on hab intervalIntegrable_const hint
      (fun x hx => (hpt x hx).1)
    simpa using this
  have hhi : (∫ x in a..(a + 1), (-σ - 1) * x ^ (-σ - 2) * ((x - a) * (x - (a + 1)) / 2))
      ≤ (σ + 1) * a ^ (-σ - 2) / 8 := by
    have := intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
      (fun x hx => (hpt x hx).2)
    simpa using this
  rw [hI]
  constructor <;> linarith

/-! ### Telescoping and the tail -/

/-- Telescoped partial sums (real version of `sum_w`). -/
lemma sum_wR (σ : ℝ) (M : ℕ) :
    ∑ n ∈ Finset.range M, wR ((n : ℝ) + 1) σ
      = σ * (1 - ((M : ℝ) + 1) ^ (1 - σ))
        - (σ - 1) * ((∑ n ∈ Finset.range M, ((n : ℝ) + 1) ^ (-σ)) - M * ((M : ℝ) + 1) ^ (-σ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    unfold wR
    push_cast
    ring

/-- The telescoping series `∑_k ((N+k)^{-p} - (N+k+1)^{-p}) = N^{-p}`. -/
lemma hasSum_rpow_telescope {p : ℝ} (hp : 0 < p) {N : ℝ} (hN : 0 < N) :
    HasSum (fun k : ℕ => (N + k) ^ (-p) - (N + k + 1) ^ (-p)) (N ^ (-p)) := by
  have hnn : ∀ k : ℕ, 0 ≤ (N + k) ^ (-p) - (N + k + 1) ^ (-p) := by
    intro k
    have h1 : 0 < N + k := by positivity
    have h2 : 0 < N + k + 1 := by positivity
    have := (Real.rpow_le_rpow_iff_of_neg (x := N + k + 1) (y := N + k) (z := -p) h2 h1
      (by linarith)).mpr (by linarith)
    linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hsum : ∀ n : ℕ, ∑ k ∈ Finset.range n, ((N + k) ^ (-p) - (N + k + 1) ^ (-p))
      = N ^ (-p) - (N + n) ^ (-p) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring_nf
  simp_rw [hsum]
  have : Tendsto (fun n : ℕ => (N + (n : ℝ)) ^ (-p)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hp).comp
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  simpa using tendsto_const_nhds.sub this

/-- `(x+1)^{-p-1} ≤ (x^{-p} - (x+1)^{-p}) / p` for `x > 0`, `p > 0`. -/
lemma rpow_succ_le_sub_div {p : ℝ} (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    (x + 1) ^ (-p - 1) ≤ (x ^ (-p) - (x + 1) ^ (-p)) / p := by
  have hI : ∫ t in x..(x + 1), t ^ (-p - 1) = (x ^ (-p) - (x + 1) ^ (-p)) / p := by
    have h1 : -p - 1 ≠ -1 := by intro h; linarith
    rw [integral_rpow (Or.inr ⟨h1, zero_notMem_uIcc hx⟩), show -p - 1 + 1 = -p by ring,
      div_eq_div_iff (neg_ne_zero.mpr hp.ne') hp.ne']
    ring
  have hmono : (x + 1) ^ (-p - 1) ≤ ∫ t in x..(x + 1), t ^ (-p - 1) := by
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (a := x) (b := x + 1)
      (f := fun _ => (x + 1) ^ (-p - 1)) (g := fun t => t ^ (-p - 1)) (by linarith)
      intervalIntegrable_const (intervalIntegrable_rpow (Or.inr (zero_notMem_uIcc hx)))
      (fun t ht => by
        rw [Set.mem_Icc] at ht
        exact (Real.rpow_le_rpow_iff_of_neg (by linarith) (by linarith) (by linarith)).mpr ht.2)
    simpa using this
  rw [← hI]
  exact hmono

/-- Tail bound: `∑_k (N+k)^{-p-1} ≤ N^{-p-1} + N^{-p}/p` for `N ≥ 1`, `p > 0`. -/
lemma tsum_rpow_tail_le {p : ℝ} (hp : 0 < p) {N : ℝ} (hN : 1 ≤ N) :
    ∑' k : ℕ, (N + k) ^ (-p - 1) ≤ N ^ (-p - 1) + N ^ (-p) / p := by
  have hN0 : 0 < N := by linarith
  have hf : Summable fun k : ℕ => (N + k) ^ (-p - 1) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (summable_rpow_add_one (-p - 1) (by linarith))
    exact (Real.rpow_le_rpow_iff_of_neg (by positivity) (by positivity) (by linarith)).mpr
      (by linarith)
  rw [hf.tsum_eq_zero_add]
  have hg := (hasSum_rpow_telescope hp hN0).div_const p
  have hle : ∀ k : ℕ, (N + ((k + 1 : ℕ) : ℝ)) ^ (-p - 1)
      ≤ ((N + k) ^ (-p) - (N + k + 1) ^ (-p)) / p := by
    intro k
    have := rpow_succ_le_sub_div hp (x := N + k) (by positivity)
    rw [Nat.cast_add_one, ← add_assoc]
    exact this
  have := Summable.tsum_le_tsum hle ((summable_nat_add_iff 1).mpr hf) hg.summable
  rw [hg.tsum_eq] at this
  simp only [Nat.cast_zero, add_zero]
  linarith

/-! ### Euler–Maclaurin with explicit remainder -/

/-- The tail `∑_k wR (N+k) σ` with `N = M+1`, in closed form up to `V = ∑_k vR (N+k) σ`. -/
lemma hasSum_wR_tail {σ : ℝ} (hσ : 0 < σ) (M : ℕ) :
    HasSum (fun k : ℕ => wR (((M : ℝ) + 1) + k) σ)
      ((σ - 1) * ((M : ℝ) + 1) ^ (-σ) / 2
        + σ * (σ - 1) * ∑' k : ℕ, vR (((M : ℝ) + 1) + k) σ) := by
  have hN0 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hv : Summable fun k : ℕ => vR (((M : ℝ) + 1) + k) σ := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => (σ + 1) * ((M : ℝ) + 1 + k) ^ (-σ - 2) / 8)
      ?_ ?_
    · have := (summable_rpow_add_one (-σ - 2) (by linarith))
      have h2 : Summable fun k : ℕ => (((M : ℝ) + 1) + k) ^ (-σ - 2) := by
        refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) this
        exact (Real.rpow_le_rpow_iff_of_neg (by positivity) (by positivity) (by linarith)).mpr
          (by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])
      exact (h2.mul_left (σ + 1)).div_const 8
    · intro k
      obtain ⟨h1, h2⟩ := vR_bounds (a := (M : ℝ) + 1 + k) (by positivity) hσ
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
  have htel := (hasSum_rpow_telescope hσ hN0).mul_left ((σ - 1) / 2)
  have h := htel.add (hv.hasSum.mul_left (σ * (σ - 1)))
  convert h using 1
  · ext k
    rw [wR_eq_vR (by positivity) σ]
    ring
  · ring

/-- **Euler–Maclaurin with explicit remainder**, about Mathlib's `riemannZeta`: for real `σ > 0`,
`σ ≠ 1` and `N = M + 1`,
`ζ(σ) = ∑_{n=1}^{M} n^{-σ} + N^{1-σ}/(σ-1) + N^{-σ}/2 + R` with `0 ≤ R ≤ σ(σ+2)/8 · N^{-σ-1}`.
In particular `riemannZeta σ` is real. -/
theorem riemannZeta_ofReal_eulerMaclaurin {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (M : ℕ) :
    ∃ R : ℝ, riemannZeta σ = (((∑ n ∈ Finset.range M, ((n : ℝ) + 1) ^ (-σ))
        + ((M : ℝ) + 1) ^ (1 - σ) / (σ - 1) + ((M : ℝ) + 1) ^ (-σ) / 2 + R : ℝ) : ℂ)
      ∧ 0 ≤ R ∧ R ≤ σ * (σ + 2) / 8 * ((M : ℝ) + 1) ^ (-σ - 1) := by
  set N : ℝ := (M : ℝ) + 1 with hN
  have hN0 : 0 < N := by positivity
  have hN1 : 1 ≤ N := by simp [hN]
  set V : ℝ := ∑' k : ℕ, vR (N + k) σ with hV
  refine ⟨-σ * V, ?_, ?_, ?_⟩
  · rw [riemannZeta_ofReal_eq hσ hσ1]
    congr 1
    -- split WR at M
    have hsplit := (summable_wR hσ).sum_add_tsum_nat_add M
    have htail : ∑' k : ℕ, wR (((k + M : ℕ) : ℝ) + 1) σ
        = (σ - 1) * N ^ (-σ) / 2 + σ * (σ - 1) * V := by
      rw [← (hasSum_wR_tail hσ M).tsum_eq]
      congr 1
      ext k
      congr 1
      push_cast
      ring
    rw [WR, ← hsplit, htail, sum_wR]
    have hσ1' : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ1
    have hpow : N ^ (1 - σ) = N ^ (-σ) * N := by
      rw [show 1 - σ = -σ + 1 by ring, Real.rpow_add_one hN0.ne']
    rw [hpow]
    field_simp
    ring
  · have : V ≤ 0 := tsum_nonpos fun k => (vR_bounds (by positivity) hσ).2
    nlinarith
  · have hVlo : -((σ + 1) / 8 * ∑' k : ℕ, (N + k) ^ (-σ - 2)) ≤ V := by
      have hsum : Summable fun k : ℕ => (N + k) ^ (-σ - 2) := by
        refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
          (summable_rpow_add_one (-σ - 2) (by linarith))
        exact (Real.rpow_le_rpow_iff_of_neg (by positivity) (by positivity) (by linarith)).mpr
          (by linarith)
      have hv : Summable fun k : ℕ => vR (N + k) σ := by
        refine Summable.of_norm_bounded (g := fun k : ℕ => (σ + 1) / 8 * (N + k) ^ (-σ - 2)) ?_ ?_
        · exact hsum.mul_left _
        · intro k
          obtain ⟨h1, h2⟩ := vR_bounds (a := N + k) (by positivity) hσ
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith
      rw [← tsum_mul_left, ← tsum_neg]
      refine Summable.tsum_le_tsum (fun k => ?_) (hsum.mul_left _).neg hv
      have := (vR_bounds (a := N + k) (by positivity) hσ).1
      linarith
    have htail := tsum_rpow_tail_le (p := σ + 1) (by linarith) hN1
    rw [show -(σ + 1) - 1 = -σ - 2 by ring, show -(σ + 1) = -σ - 1 by ring] at htail
    have hpow : N ^ (-σ - 2) ≤ N ^ (-σ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hT : ∑' k : ℕ, (N + k) ^ (-σ - 2) ≤ (σ + 2) / (σ + 1) * N ^ (-σ - 1) := by
      calc ∑' k : ℕ, (N + k) ^ (-σ - 2) ≤ N ^ (-σ - 2) + N ^ (-σ - 1) / (σ + 1) := htail
        _ ≤ N ^ (-σ - 1) + N ^ (-σ - 1) / (σ + 1) := by linarith
        _ = (σ + 2) / (σ + 1) * N ^ (-σ - 1) := by field_simp; ring
    have hpos : 0 ≤ N ^ (-σ - 1) := by positivity
    calc -σ * V ≤ σ * ((σ + 1) / 8 * ∑' k : ℕ, (N + k) ^ (-σ - 2)) := by nlinarith
      _ ≤ σ * ((σ + 1) / 8 * ((σ + 2) / (σ + 1) * N ^ (-σ - 1))) := by gcongr
      _ = σ * (σ + 2) / 8 * N ^ (-σ - 1) := by field_simp

end CN1.Numerics
