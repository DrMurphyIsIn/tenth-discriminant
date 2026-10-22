import CN1.ChowlaSelberg.PoissonSlice

/-!
# CN1.ChowlaSelberg.Remainder: the remainder `E_d(s)` and its bound

  `Rterm d s (y, k) = (-1)^{kby} I(s; a_y, b_k)`  (`0` if `y = 0` or `k = 0`),
  `S d s = Σ_{(y,k) ∈ ℤ²} Rterm d s (y, k)`,
  `E d s = π^s / (2 Γ(s)) · S d s`.

Main facts (`d ≥ 3`):
* `norm_Rterm_le`: for `re s > 1/2`, `‖Rterm d s (y,k)‖ ≤ Γ(σ - 1/2) (8/(πd))^{σ - 1/2} g(y) g(k)`
  with `g(n) = e^{-(c/2)|n|}` (`n ≠ 0`), `c = π √d / 2`, from the AM–GM bound of `GammaIntegral.lean`,
  `√(a_y b_k) = c |y| |k|`, and `|y| |k| ≥ (|y| + |k|)/2`.
* `differentiableOn_E`: `E d` is holomorphic on `re s > 1/2` (uniform majorant on strips, with
  `Γ` bounded there by convexity; `1/Γ(s)` is kept outside the sum).
* `E_ofReal_im`: `E d σ` is real for real `σ`.
* `norm_E_seven_eighths_le`: `‖E d (7/8)‖ ≤ B d`, where
  `B d = 2 π^{7/8} Γ(3/8)/Γ(7/8) · (8/(πd))^{3/8} · e^{-c} / (1 - e^{-c/2})²`.
  (Slightly weaker than the sharper bound whose denominator is `(1 - e^{-c})²`; the product
  majorant costs the factor `c/2` in the exponent of the denominator only.)
* `B_le_B0` (`d ≥ 7`): `B d ≤ B0 d = 4 π^{7/8} Γ(3/8)/Γ(7/8) (8/(πd))^{3/8} e^{-π√d/2}`;
  `B0_antitone`; `B0_le_B1` (`d ≥ 3`): `B0 d ≤ 4 π^{7/8} Γ(3/8)/Γ(7/8) e^{-π√d/2}`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped Real

namespace CN1.CS

variable {d : ℕ}

/-- `c_d = π √d / 2`, the exponent in `e^{-c |y| |k|}`. -/
noncomputable def cst (d : ℕ) : ℝ := π * Real.sqrt d / 2

/-- The `(y, k)` term of the remainder: `(-1)^{kby} I(s; a_y, b_k)`, and `0` if `y = 0 ∨ k = 0`. -/
noncomputable def Rterm (d : ℕ) (s : ℂ) (p : ℤ × ℤ) : ℂ :=
  if p.1 = 0 ∨ p.2 = 0 then 0 else sgn d p.2 p.1 * I s (ay d p.1) (bk p.2)

/-- `S_d(s) = Σ_{y ≠ 0} Σ_{k ≠ 0} (-1)^{kby} I(s; a_y, b_k)`, as a sum over `ℤ²`. -/
noncomputable def S (d : ℕ) (s : ℂ) : ℂ := ∑' p : ℤ × ℤ, Rterm d s p

/-- The Chowla–Selberg remainder `E_d(s) = π^s / (2 Γ(s)) · S_d(s)`. -/
noncomputable def E (d : ℕ) (s : ℂ) : ℂ := (π : ℂ) ^ s * (Gamma s)⁻¹ / 2 * S d s

/-- The one-variable majorant `g_c(n) = e^{-c|n|}` for `n ≠ 0`, and `0` at `n = 0`. -/
noncomputable def gmaj (c : ℝ) (n : ℤ) : ℝ := if n = 0 then 0 else Real.exp (-(c * |(n : ℝ)|))

/-- The bound `B(d)` on `|E_d(7/8)|`. -/
noncomputable def B (d : ℕ) : ℝ :=
  2 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * (8 / (π * d)) ^ (3 / 8 : ℝ) *
    (Real.exp (-cst d) / (1 - Real.exp (-(cst d / 2))) ^ 2)

/-- The simpler bound `B₀(d) = 4 π^{7/8} Γ(3/8)/Γ(7/8) (8/(πd))^{3/8} e^{-π√d/2}` (valid for `d ≥ 7`). -/
noncomputable def B0 (d : ℕ) : ℝ :=
  4 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * (8 / (π * d)) ^ (3 / 8 : ℝ) *
    Real.exp (-(π * Real.sqrt d / 2))

/-- The crudest bound `B₁(d) = 4 π^{7/8} Γ(3/8)/Γ(7/8) e^{-π√d/2}` (valid for `d ≥ 7`). -/
noncomputable def B1 (d : ℕ) : ℝ :=
  4 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * Real.exp (-(π * Real.sqrt d / 2))

/-! ### The majorant `g` -/

lemma cst_pos (hd : 1 ≤ d) : 0 < cst d := by
  unfold cst
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

lemma gmaj_nonneg (c : ℝ) (n : ℤ) : 0 ≤ gmaj c n := by
  unfold gmaj; split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

lemma gmaj_le (c : ℝ) (n : ℤ) : gmaj c n ≤ Real.exp (-(c * |(n : ℝ)|)) := by
  unfold gmaj; split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

lemma summable_gmaj {c : ℝ} (hc : 0 < c) : Summable (gmaj c) :=
  Summable.of_nonneg_of_le (gmaj_nonneg c) (gmaj_le c) (summable_exp_neg_mul_abs_int hc)

lemma gmaj_even (c : ℝ) : Function.Even (gmaj c) := by
  intro n
  simp [gmaj, abs_neg]

lemma gmaj_zero (c : ℝ) : gmaj c 0 = 0 := by simp [gmaj]

/-- `Σ_{n ∈ ℤ} g_c(n) = 2 e^{-c} / (1 - e^{-c})`. -/
lemma tsum_gmaj {c : ℝ} (hc : 0 < c) :
    ∑' n : ℤ, gmaj c n = 2 * (Real.exp (-c) / (1 - Real.exp (-c))) := by
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (gmaj_even c) (summable_gmaj hc), gmaj_zero, zero_add,
    nsmul_eq_mul, Nat.cast_ofNat]
  congr 1
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => gmaj c (n : ℤ))]
  have h : ∀ n : ℕ, gmaj c ((n + 1 : ℕ) : ℤ) = Real.exp (-c) * Real.exp (-c) ^ n := by
    intro n
    have hne : ((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
    rw [gmaj, if_neg hne, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [Int.cast_natCast, abs_of_nonneg (by positivity)]
    push_cast
    ring
  simp_rw [h]
  rw [tsum_mul_left,
    tsum_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith)),
    div_eq_mul_inv]

lemma summable_maj (hd : 1 ≤ d) (C : ℝ) :
    Summable fun p : ℤ × ℤ => C * (gmaj (cst d / 2) p.1 * gmaj (cst d / 2) p.2) := by
  have hc : 0 < cst d / 2 := by have := cst_pos hd; positivity
  exact ((summable_gmaj hc).mul_of_nonneg (summable_gmaj hc) (gmaj_nonneg _)
    (gmaj_nonneg _)).mul_left C

/-! ### Elementary estimates on `a_y`, `b_k` -/

lemma sqrt_ay_bk (hd : 1 ≤ d) (y k : ℤ) :
    Real.sqrt (ay d y * bk k) = cst d * |(y : ℝ)| * |(k : ℝ)| := by
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have h : ay d y * bk k = (cst d * |(y : ℝ)| * |(k : ℝ)|) ^ 2 := by
    unfold ay bk cst
    simp only [mul_pow, sq_abs, div_pow, Real.sq_sqrt hd0]
    ring
  rw [h, Real.sqrt_sq (mul_nonneg (mul_nonneg (cst_pos hd).le (abs_nonneg _)) (abs_nonneg _))]

lemma two_div_ay_le (hd : 1 ≤ d) {y : ℤ} (hy : y ≠ 0) : 2 / ay d y ≤ 8 / (π * d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hy1 : (1 : ℝ) ≤ |(y : ℝ)| := by exact_mod_cast Int.one_le_abs hy
  have hy2 : (1 : ℝ) ≤ (y : ℝ) ^ 2 := by nlinarith [sq_abs (y : ℝ)]
  have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  have e : 2 / ay d y = 8 / (π * d * (y : ℝ) ^ 2) := by
    unfold ay
    field_simp
    ring
  rw [e]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (le_mul_of_one_le_right (by positivity) hy2)

lemma eight_div_le_one (hd3 : 3 ≤ d) : 8 / (π * d) ≤ 1 := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd3
  rw [div_le_one (by positivity)]
  nlinarith [Real.pi_gt_three]

/-! ### The termwise bound -/

/-- **Termwise bound.** For `re s > 1/2`,
`‖Rterm d s (y,k)‖ ≤ Γ(σ - 1/2) (8/(πd))^{σ - 1/2} g(y) g(k)`, `g(n) = e^{-(c/2)|n|}`. -/
theorem norm_Rterm_le (hd3 : 3 ≤ d) {s : ℂ} (hs : 1 / 2 < s.re) (p : ℤ × ℤ) :
    ‖Rterm d s p‖ ≤ Real.Gamma (s.re - 1 / 2) * (8 / (π * d)) ^ (s.re - 1 / 2) *
      (gmaj (cst d / 2) p.1 * gmaj (cst d / 2) p.2) := by
  have hd1 : 1 ≤ d := by omega
  have hΓ : 0 ≤ Real.Gamma (s.re - 1 / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  have h8 : 0 ≤ (8 / (π * d)) ^ (s.re - 1 / 2) := Real.rpow_nonneg (by positivity) _
  have hg : 0 ≤ gmaj (cst d / 2) p.1 * gmaj (cst d / 2) p.2 :=
    mul_nonneg (gmaj_nonneg _ _) (gmaj_nonneg _ _)
  unfold Rterm
  split_ifs with h
  · rw [norm_zero]; exact mul_nonneg (mul_nonneg hΓ h8) hg
  · push_neg at h
    obtain ⟨hy, hk⟩ := h
    rw [norm_mul, norm_sgn, one_mul]
    have hay := ay_pos hd3 hy
    refine (norm_I_le hay (bk_nonneg _) hs).trans ?_
    rw [sqrt_ay_bk hd1]
    have hc := cst_pos hd1
    have hy1 : (1 : ℝ) ≤ |(p.1 : ℝ)| := by exact_mod_cast Int.one_le_abs hy
    have hk1 : (1 : ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have hexp : Real.exp (-(cst d * |(p.1 : ℝ)| * |(p.2 : ℝ)|)) ≤
        gmaj (cst d / 2) p.1 * gmaj (cst d / 2) p.2 := by
      simp only [gmaj, if_neg hy, if_neg hk]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have key : |(p.1 : ℝ)| + |(p.2 : ℝ)| ≤ 2 * (|(p.1 : ℝ)| * |(p.2 : ℝ)|) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr hk1)]
      nlinarith [mul_le_mul_of_nonneg_left key hc.le]
    have hpow : (2 / ay d p.1) ^ (s.re - 1 / 2) ≤ (8 / (π * d)) ^ (s.re - 1 / 2) :=
      Real.rpow_le_rpow (by positivity) (two_div_ay_le hd1 hy) (by linarith)
    calc Real.exp (-(cst d * |(p.1 : ℝ)| * |(p.2 : ℝ)|)) *
          ((2 / ay d p.1) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2))
        ≤ (gmaj (cst d / 2) p.1 * gmaj (cst d / 2) p.2) *
          ((8 / (π * d)) ^ (s.re - 1 / 2) * Real.Gamma (s.re - 1 / 2)) :=
          mul_le_mul hexp (mul_le_mul_of_nonneg_right hpow hΓ) (by positivity) hg
      _ = _ := by ring

theorem summable_norm_Rterm (hd3 : 3 ≤ d) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable fun p : ℤ × ℤ => ‖Rterm d s p‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_Rterm_le hd3 hs)
    (summable_maj (by omega) _)

theorem summable_Rterm (hd3 : 3 ≤ d) {s : ℂ} (hs : 1 / 2 < s.re) : Summable (Rterm d s) :=
  (summable_norm_Rterm hd3 hs).of_norm

/-- `S d s` as an iterated sum `Σ_y Σ_k`. -/
theorem S_eq_tsum_tsum (hd3 : 3 ≤ d) {s : ℂ} (hs : 1 / 2 < s.re) :
    S d s = ∑' y : ℤ, ∑' k : ℤ, Rterm d s (y, k) :=
  (summable_Rterm hd3 hs).tsum_prod' fun y => (summable_Rterm hd3 hs).prod_factor y

/-! ### Holomorphy of `E_d` on `re s > 1/2` -/

lemma differentiableOn_Rterm (hd3 : 3 ≤ d) (p : ℤ × ℤ) :
    DifferentiableOn ℂ (fun s => Rterm d s p) {s : ℂ | 1 / 2 < s.re} := by
  by_cases h : p.1 = 0 ∨ p.2 = 0
  · simp only [Rterm, if_pos h]
    exact differentiableOn_const 0
  · simp only [Rterm, if_neg h]
    push_neg at h
    intro s hs
    exact ((differentiableAt_I (ay_pos hd3 h.1) (bk_nonneg _) hs).const_mul _).differentiableWithinAt

theorem differentiableAt_S (hd3 : 3 ≤ d) {s₀ : ℂ} (hs₀ : 1 / 2 < s₀.re) :
    DifferentiableAt ℂ (S d) s₀ := by
  set δ : ℝ := (s₀.re - 1 / 2) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set U : Set ℂ := {s | s₀.re - δ < s.re} ∩ {s | s.re < s₀.re + δ} with hU
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hs₀U : s₀ ∈ U := ⟨by simp only [mem_setOf_eq]; linarith, by simp only [mem_setOf_eq]; linarith⟩
  have hUsub : U ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    obtain ⟨h1, _⟩ := hs
    simp only [mem_setOf_eq] at h1 ⊢
    linarith
  set CΓ : ℝ := max (Real.Gamma δ) (Real.Gamma (3 * δ)) with hCΓ
  have hCΓ0 : 0 ≤ CΓ := le_max_of_le_left (Real.Gamma_pos_of_pos hδpos).le
  have hΓle : ∀ s ∈ U, Real.Gamma (s.re - 1 / 2) ≤ CΓ := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    simp only [mem_setOf_eq] at h1 h2
    apply Real.convexOn_Gamma.le_on_segment (mem_Ioi.mpr hδpos) (mem_Ioi.mpr (by linarith))
    rw [segment_eq_Icc (by linarith)]
    exact ⟨by linarith, by linarith⟩
  have hsum := summable_maj (by omega : 1 ≤ d) CΓ
  have hdiff : DifferentiableOn ℂ (fun w => ∑' p : ℤ × ℤ, Rterm d w p) U := by
    refine differentiableOn_tsum_of_summable_norm hsum
      (fun p => (differentiableOn_Rterm hd3 p).mono hUsub) hUopen (fun p w hw => ?_)
    have hw' : 1 / 2 < w.re := hUsub hw
    refine (norm_Rterm_le hd3 hw' p).trans ?_
    have h8 : (8 / (π * d)) ^ (w.re - 1 / 2) ≤ 1 :=
      Real.rpow_le_one (by positivity) (eight_div_le_one hd3) (by linarith)
    have h80 : 0 ≤ (8 / (π * d)) ^ (w.re - 1 / 2) := Real.rpow_nonneg (by positivity) _
    have hΓ0 : 0 ≤ Real.Gamma (w.re - 1 / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
    have hg : 0 ≤ gmaj (cst d / 2) p.1 * gmaj (cst d / 2) p.2 :=
      mul_nonneg (gmaj_nonneg _ _) (gmaj_nonneg _ _)
    calc Real.Gamma (w.re - 1 / 2) * (8 / (π * d)) ^ (w.re - 1 / 2) *
          (gmaj (cst d / 2) p.1 * gmaj (cst d / 2) p.2)
        ≤ CΓ * 1 * (gmaj (cst d / 2) p.1 * gmaj (cst d / 2) p.2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hΓle w hw) h8 h80 hCΓ0) hg
      _ = CΓ * (gmaj (cst d / 2) p.1 * gmaj (cst d / 2) p.2) := by ring
  exact hdiff.differentiableAt (hUopen.mem_nhds hs₀U)

theorem differentiableAt_E (hd3 : 3 ≤ d) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (E d) s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (π : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr Real.pi_pos.ne'))
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (Gamma s)⁻¹) s := Complex.differentiable_one_div_Gamma s
  exact ((h1.mul h2).div_const 2).mul (differentiableAt_S hd3 hs)

theorem differentiableOn_E (hd3 : 3 ≤ d) : DifferentiableOn ℂ (E d) {s : ℂ | 1 / 2 < s.re} :=
  fun _ hs => (differentiableAt_E hd3 hs).differentiableWithinAt

/-! ### `E_d(σ)` is real for real `σ` -/

/-- The real integral `∫₀^∞ t^{σ - 3/2} e^{-a t - b/t} dt`. -/
noncomputable def IR (σ a b : ℝ) : ℝ := ∫ t in Ioi 0, t ^ (σ - 3 / 2) * Real.exp (-(a * t + b / t))

/-- The real `(y, k)` term. -/
noncomputable def RtermR (d : ℕ) (σ : ℝ) (p : ℤ × ℤ) : ℝ :=
  if p.1 = 0 ∨ p.2 = 0 then 0 else (-1 : ℝ) ^ (p.2 * (bq d : ℤ) * p.1) * IR σ (ay d p.1) (bk p.2)

lemma Rterm_ofReal (σ : ℝ) (p : ℤ × ℤ) : Rterm d (σ : ℂ) p = (RtermR d σ p : ℂ) := by
  unfold Rterm RtermR
  split_ifs
  · simp
  · rw [sgn, I_ofReal]
    unfold IR
    push_cast
    ring

lemma S_ofReal (σ : ℝ) : S d (σ : ℂ) = ((∑' p : ℤ × ℤ, RtermR d σ p : ℝ) : ℂ) := by
  rw [S, Complex.ofReal_tsum]
  exact tsum_congr fun p => Rterm_ofReal σ p

theorem E_ofReal (σ : ℝ) :
    E d (σ : ℂ) = ((π ^ σ * (Real.Gamma σ)⁻¹ / 2 * ∑' p : ℤ × ℤ, RtermR d σ p : ℝ) : ℂ) := by
  rw [E, S_ofReal, ← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal]
  push_cast
  ring

theorem E_ofReal_im (σ : ℝ) : (E d (σ : ℂ)).im = 0 := by
  rw [E_ofReal, ofReal_im]

theorem E_seven_eighths_im : (E d (7 / 8)).im = 0 := by
  have h : ((7 / 8 : ℝ) : ℂ) = (7 / 8 : ℂ) := by push_cast; ring
  rw [← h, E_ofReal_im]

/-! ### The bound at `s = 7/8` -/

lemma seven_eighths_re : (7 / 8 : ℂ).re = 7 / 8 := by norm_num

theorem norm_S_seven_eighths_le (hd3 : 3 ≤ d) :
    ‖S d (7 / 8)‖ ≤ Real.Gamma (3 / 8) * (8 / (π * d)) ^ (3 / 8 : ℝ) *
      (2 * (Real.exp (-(cst d / 2)) / (1 - Real.exp (-(cst d / 2))))) ^ 2 := by
  have hs : 1 / 2 < (7 / 8 : ℂ).re := by rw [seven_eighths_re]; norm_num
  have hre : (7 / 8 : ℂ).re - 1 / 2 = 3 / 8 := by rw [seven_eighths_re]; norm_num
  have hc : 0 < cst d / 2 := by have := cst_pos (by omega : 1 ≤ d); positivity
  calc ‖S d (7 / 8)‖ ≤ ∑' p : ℤ × ℤ, ‖Rterm d (7 / 8) p‖ :=
        norm_tsum_le_tsum_norm (summable_norm_Rterm hd3 hs)
    _ ≤ ∑' p : ℤ × ℤ, Real.Gamma (3 / 8) * (8 / (π * d)) ^ (3 / 8 : ℝ) *
          (gmaj (cst d / 2) p.1 * gmaj (cst d / 2) p.2) := by
        refine Summable.tsum_le_tsum (fun p => ?_) (summable_norm_Rterm hd3 hs)
          (summable_maj (by omega) _)
        have := norm_Rterm_le hd3 hs p
        rwa [hre] at this
    _ = Real.Gamma (3 / 8) * (8 / (π * d)) ^ (3 / 8 : ℝ) *
          ((∑' n : ℤ, gmaj (cst d / 2) n) * ∑' n : ℤ, gmaj (cst d / 2) n) := by
        rw [tsum_mul_left, (summable_gmaj hc).tsum_mul_tsum (summable_gmaj hc)
          ((summable_gmaj hc).mul_of_nonneg (summable_gmaj hc) (gmaj_nonneg _) (gmaj_nonneg _))]
    _ = _ := by rw [tsum_gmaj hc]; ring

/-- **The remainder bound at `s = 7/8`:** `‖E_d(7/8)‖ ≤ B(d)`. -/
theorem norm_E_seven_eighths_le (hd3 : 3 ≤ d) : ‖E d (7 / 8)‖ ≤ B d := by
  have hd1 : 1 ≤ d := by omega
  have hc : 0 < cst d / 2 := by have := cst_pos hd1; positivity
  have hπ : ‖(π : ℂ) ^ (7 / 8 : ℂ)‖ = π ^ (7 / 8 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, seven_eighths_re]
  have hG : Gamma (7 / 8 : ℂ) = (Real.Gamma (7 / 8) : ℂ) := by
    rw [← Complex.Gamma_ofReal]
    congr 1
    push_cast
    ring
  have hGpos : 0 < Real.Gamma (7 / 8) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hq : Real.exp (-(cst d / 2)) ^ 2 = Real.exp (-cst d) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hq1 : 0 < 1 - Real.exp (-(cst d / 2)) := by
    have := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hc)
    linarith
  have hK : 0 ≤ π ^ (7 / 8 : ℝ) * (Real.Gamma (7 / 8))⁻¹ / 2 := by positivity
  rw [E, norm_mul, norm_div, norm_mul, hπ, hG, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hGpos, h2]
  calc π ^ (7 / 8 : ℝ) * (Real.Gamma (7 / 8))⁻¹ / 2 * ‖S d (7 / 8)‖
      ≤ π ^ (7 / 8 : ℝ) * (Real.Gamma (7 / 8))⁻¹ / 2 *
        (Real.Gamma (3 / 8) * (8 / (π * d)) ^ (3 / 8 : ℝ) *
          (2 * (Real.exp (-(cst d / 2)) / (1 - Real.exp (-(cst d / 2))))) ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_S_seven_eighths_le hd3) hK
    _ = B d := by
        rw [B, mul_pow, div_pow, hq]
        field_simp

/-! ### Comparison bounds and monotonicity -/

lemma exp_neg_half_cst_le (hd : 7 ≤ d) : Real.exp (-(cst d / 2)) ≤ 1 / 4 := by
  have hd' : (7 : ℝ) ≤ d := by exact_mod_cast hd
  have hsqrt : (2.64 : ℝ) ≤ Real.sqrt d :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hc4 : (1 : ℝ) ≤ cst d / 4 := by
    unfold cst
    nlinarith [Real.pi_gt_d2]
  have h1 := Real.add_one_le_exp (cst d / 4)
  have h2 : (2 : ℝ) ≤ Real.exp (cst d / 4) := by linarith
  have h3 : (4 : ℝ) ≤ Real.exp (cst d / 2) := by
    have e : Real.exp (cst d / 2) = Real.exp (cst d / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    nlinarith
  rw [Real.exp_neg]
  calc (Real.exp (cst d / 2))⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h3
    _ = 1 / 4 := by norm_num

/-- `B d ≤ B₀ d` for `d ≥ 7`. -/
theorem B_le_B0 (hd : 7 ≤ d) : B d ≤ B0 d := by
  have hq := exp_neg_half_cst_le hd
  have hq0 : 0 ≤ Real.exp (-(cst d / 2)) := (Real.exp_pos _).le
  have h1q : (1 / 2 : ℝ) ≤ (1 - Real.exp (-(cst d / 2))) ^ 2 := by nlinarith
  have he : 0 < Real.exp (-cst d) := Real.exp_pos _
  have hfrac : Real.exp (-cst d) / (1 - Real.exp (-(cst d / 2))) ^ 2 ≤ 2 * Real.exp (-cst d) := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have hK : 0 ≤ 2 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) *
      (8 / (π * d)) ^ (3 / 8 : ℝ) := by positivity
  calc B d = 2 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) *
        (8 / (π * d)) ^ (3 / 8 : ℝ) *
        (Real.exp (-cst d) / (1 - Real.exp (-(cst d / 2))) ^ 2) := rfl
    _ ≤ 2 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) *
        (8 / (π * d)) ^ (3 / 8 : ℝ) * (2 * Real.exp (-cst d)) :=
        mul_le_mul_of_nonneg_left hfrac hK
    _ = B0 d := by unfold B0 cst; ring

/-- `B₀` is antitone in `d ≥ 1`. -/
theorem B0_antitone {d d' : ℕ} (hd : 1 ≤ d) (h : d ≤ d') : B0 d' ≤ B0 d := by
  unfold B0
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdd : (d : ℝ) ≤ d' := by exact_mod_cast h
  have hK : 0 ≤ 4 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) := by positivity
  have h1 : (8 / (π * d')) ^ (3 / 8 : ℝ) ≤ (8 / (π * d)) ^ (3 / 8 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith [Real.pi_pos]))
      (by norm_num)
  have h2 : Real.exp (-(π * Real.sqrt d' / 2)) ≤ Real.exp (-(π * Real.sqrt d / 2)) := by
    apply Real.exp_le_exp.mpr
    have := Real.sqrt_le_sqrt hdd
    nlinarith [Real.pi_pos]
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hK) h2 (Real.exp_pos _).le (by positivity)

/-- `B₀ d ≤ B₁ d` for `d ≥ 3`. -/
theorem B0_le_B1 (hd3 : 3 ≤ d) : B0 d ≤ B1 d := by
  unfold B0 B1
  have hK : 0 ≤ 4 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) := by positivity
  have h8 : (8 / (π * d)) ^ (3 / 8 : ℝ) ≤ 1 :=
    Real.rpow_le_one (by positivity) (eight_div_le_one hd3) (by norm_num)
  calc 4 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * (8 / (π * d)) ^ (3 / 8 : ℝ) *
        Real.exp (-(π * Real.sqrt d / 2))
      ≤ 4 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * 1 *
        Real.exp (-(π * Real.sqrt d / 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h8 hK) (Real.exp_pos _).le
    _ = _ := by ring

end CN1.CS
