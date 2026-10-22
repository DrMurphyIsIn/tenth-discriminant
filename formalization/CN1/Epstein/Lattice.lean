import CN1.Foundations.Basic
import CN1.Epstein.IdealCount

/-!
# `h = 1 ⇒ ζ_K(s) = ½ Σ′ Q(x,y)^{-s}` on `Re s > 1` (step 1 of the argument)

Pinned environment: Lean v4.34.1, Mathlib d13f23b.

For the statement's `K` (`finrank 2`, `α² = -m`, `m` squarefree, `m ∉ {1, 3}`) with class number one:
every ideal is principal, the units are `±1`, and `N(x + yω) = Q(x, y)` with `Q = principalForm m`
(both from `CN1.Foundations.Basic`). So `(x, y) ↦ (x + yω)` is a 2-to-1 map from `ℤ² ∖ 0` onto the nonzero ideals, preserving the
norm, and regrouping the lattice sum by the norm gives `Σ′ Q^{-s} = 2 Σ_n a_K(n) n^{-s} = 2 ζ_K(s)`.

Formally: `ℤ² ≃ 𝓞 K` (`intPairEquiv`), the `(0,0)` term is `0 ^ (-s) = 0`, the lattice sum converges
absolutely for `Re s > 1` (`summable_principalForm_cpow`, by comparison with `Σ ‖v‖^{-2σ}` as in
openai/math's `LatticeSummability` and `CN1.ChowlaSelberg.Form`), and `HasSum.tsum_fiberwise` along
`z ↦ |N(z)|` regroups it; the fibre over `n ≥ 1` has `2 · a_K(n)` elements
(`card_nonzero_normNat_eq`: `(𝓞 K)ˣ × {I : N(I) = n} ≃ {z ≠ 0 : |N(z)| = n}`, `(u, I) ↦ u · gen(I)`).
-/

set_option autoImplicit false

namespace CN1.Epstein

open NumberField Ideal CN1.Foundations

/-! ### Absolute convergence of the lattice sum -/

section Summability

variable {m : ℕ}

/-- `Q(x, y) ≥ (x² + y²) / 2` for the principal form (as reals), once `m ≥ 1`. -/
theorem half_sq_add_sq_le_principalForm (hm0 : m ≠ 0) (x y : ℤ) :
    ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) / 2 ≤ ((principalForm m x y : ℤ) : ℝ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
  unfold principalForm
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : (m + 1) / 4 = c := by omega
    have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast (show 1 ≤ c by omega)
    rw [hc']
    push_cast
    nlinarith [sq_nonneg ((x : ℝ) + y), mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg (y : ℝ))]
  · push_cast
    nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ)]

/-- `‖v‖² ≤ x² + y²` for `v = (x, y) ∈ ℤ²` with the sup norm. -/
theorem norm_sq_le_sq_add_sq (v : ℤ × ℤ) : ‖v‖ ^ 2 ≤ (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 := by
  rw [Prod.norm_def, ← Int.norm_cast_real, ← Int.norm_cast_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  rcases le_total |(v.1 : ℝ)| |(v.2 : ℝ)| with h | h
  · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg (v.1 : ℝ)]
  · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg (v.2 : ℝ)]

/-- `Σ_{v ∈ ℤ²} ‖v‖^{-k}` converges for `k > 2` (sup norm); openai/math's pattern via
`EisensteinSeries.summable_one_div_norm_rpow`. -/
theorem summable_pair_norm_rpow {k : ℝ} (hk : 2 < k) :
    Summable (fun v : ℤ × ℤ => ‖v‖ ^ (-k)) := by
  have h := (finTwoArrowEquiv ℤ).symm.summable_iff.mpr
    (EisensteinSeries.summable_one_div_norm_rpow hk)
  have hn (n : ℤ) : (n.natAbs : ℝ) = ‖n‖ := by
    exact congrArg (fun x : NNReal => (x : ℝ)) (NNReal.natCast_natAbs n)
  simpa only [finTwoArrowEquiv_symm_apply, Function.comp_def,
    EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero,
    Matrix.cons_val_one, Prod.norm_def, Nat.cast_max, hn] using h

/-- Real form: `Σ_{v ∈ ℤ²} Q(v)^{-σ} < ∞` for `σ > 1`. -/
theorem summable_principalForm_rpow (hm0 : m ≠ 0) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun v : ℤ × ℤ => ((principalForm m v.1 v.2 : ℤ) : ℝ) ^ (-σ)) := by
  have hmajor := (summable_pair_norm_rpow (k := 2 * σ) (by linarith)).mul_left
    ((1 / 2 : ℝ) ^ (-σ))
  have hQnn : ∀ v : ℤ × ℤ, (0 : ℝ) ≤ ((principalForm m v.1 v.2 : ℤ) : ℝ) := fun v => by
    exact_mod_cast principalForm_nonneg m v.1 v.2
  refine Summable.of_nonneg_of_le (fun v => Real.rpow_nonneg (hQnn v) _) (fun v => ?_) hmajor
  by_cases hv : v = 0
  · subst hv
    simp [principalForm, Real.zero_rpow (by linarith : -σ ≠ 0),
      Real.zero_rpow (by linarith : -(2 * σ) ≠ 0)]
  · have hnpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hle : (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ ((principalForm m v.1 v.2 : ℤ) : ℝ) :=
      le_trans (by have := norm_sq_le_sq_add_sq v; linarith)
        (half_sq_add_sq_le_principalForm hm0 v.1 v.2)
    calc ((principalForm m v.1 v.2 : ℤ) : ℝ) ^ (-σ)
        ≤ ((1 / 2 : ℝ) * ‖v‖ ^ 2) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
      _ = (1 / 2 : ℝ) ^ (-σ) * ‖v‖ ^ (-(2 * σ)) := by
          rw [Real.mul_rpow (by norm_num) (sq_nonneg _)]
          congr 1
          rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
          congr 1
          ring

/-- Complex form: `Σ_{v ∈ ℤ²} Q(v)^{-s}` converges absolutely for `Re s > 1`. -/
theorem summable_principalForm_cpow (hm0 : m ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : ℤ × ℤ => ((principalForm m v.1 v.2 : ℤ) : ℂ) ^ (-s)) := by
  refine Summable.of_norm_bounded (summable_principalForm_rpow hm0 hs) fun v => ?_
  have hQnn : (0 : ℝ) ≤ ((principalForm m v.1 v.2 : ℤ) : ℝ) := by
    exact_mod_cast principalForm_nonneg m v.1 v.2
  rw [← Complex.ofReal_intCast, Complex.norm_cpow_eq_rpow_re_of_nonneg hQnn
    (by rw [Complex.neg_re]; linarith), Complex.neg_re]

end Summability

/-! ### `ℤ² ≃ 𝓞 K` and the norm -/

section Field

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
  (hK : Module.finrank ℚ K = 2) (hm : Squarefree m)

include hα hK hm in
/-- `(x, y) ↦ x + y ω` is a bijection `ℤ² ≃ 𝓞 K` (`𝓞 K = ℤ[ω]`, `CN1.Foundations.Basic`). -/
noncomputable def intPairEquiv : ℤ × ℤ ≃ 𝓞 K :=
  Equiv.ofBijective (fun v => (v.1 : 𝓞 K) + (v.2 : 𝓞 K) * omegaInt hα)
    ⟨fun v w h => Prod.ext (int_add_int_mul_omegaInt_inj hα hK hm.ne_zero h).1
        (int_add_int_mul_omegaInt_inj hα hK hm.ne_zero h).2,
      fun z => by
        obtain ⟨u, v, hz⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
        exact ⟨(u, v), hz.symm⟩⟩

include hα hK hm in
/-- `N(x + y ω) = Q(x, y)`. -/
theorem norm_intPairEquiv (v : ℤ × ℤ) :
    Algebra.norm ℤ (intPairEquiv hα hK hm v) = principalForm m v.1 v.2 :=
  norm_int_eq_principalForm hα hK hm.ne_zero rfl

include hα hK hm in
/-- The norm form is nonnegative on `𝓞 K`. -/
theorem norm_int_nonneg (z : 𝓞 K) : 0 ≤ Algebra.norm ℤ z := by
  obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
  rw [norm_int_eq_principalForm hα hK hm.ne_zero rfl]
  exact principalForm_nonneg m u v

/-- `|N(z)| = N(span {z})`. -/
theorem natAbs_norm_eq_absNorm_span (z : 𝓞 K) :
    (Algebra.norm ℤ z).natAbs = absNorm (span {z}) :=
  (absNorm_span_singleton z).symm

/-- `|N(z)| = 0 ↔ z = 0`. -/
theorem natAbs_norm_eq_zero_iff (z : 𝓞 K) : (Algebra.norm ℤ z).natAbs = 0 ↔ z = 0 := by
  rw [natAbs_norm_eq_absNorm_span, absNorm_eq_zero_iff, span_singleton_eq_bot]

include hα hK hm in
/-- `(N(z) : ℂ) = (|N(z)| : ℂ)`, the norm being nonnegative. -/
theorem norm_cast_eq_natAbs_cast (z : 𝓞 K) :
    ((Algebra.norm ℤ z : ℤ) : ℂ) = (((Algebra.norm ℤ z).natAbs : ℕ) : ℂ) := by
  rw [← Int.cast_natCast, Int.natAbs_of_nonneg (norm_int_nonneg hα hK hm z)]

/-! ### The 2-to-1 map `z ↦ (z)` when every ideal is principal -/

section PID

variable [IsPrincipalIdealRing (𝓞 K)]

open Submodule.IsPrincipal in
/-- Every `z ∈ 𝓞 K` is a unit times the chosen generator of `(z)`. -/
theorem exists_unit_mul_generator_eq (z : 𝓞 K) :
    ∃ u : (𝓞 K)ˣ, (u : 𝓞 K) * generator (span {z}) = z := by
  have h : Associated (generator (span {z})) z :=
    Ideal.span_singleton_eq_span_singleton.mp (Ideal.span_singleton_generator (span {z}))
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by rw [mul_comm]; exact hu⟩

open Submodule.IsPrincipal in
/-- The unit `u` with `z = u · gen((z))`. -/
noncomputable def unitOf (z : 𝓞 K) : (𝓞 K)ˣ := Classical.choose (exists_unit_mul_generator_eq z)

open Submodule.IsPrincipal in
theorem unitOf_spec (z : 𝓞 K) : (unitOf z : 𝓞 K) * generator (span {z}) = z :=
  Classical.choose_spec (exists_unit_mul_generator_eq z)

open Submodule.IsPrincipal in
/-- Equal ideals have equal chosen generators (`IsPrincipal` is a `Prop`). -/
theorem generator_congr {I J : Ideal (𝓞 K)} [I.IsPrincipal] [J.IsPrincipal] (h : I = J) :
    generator I = generator J := by
  subst h
  rfl

open Submodule.IsPrincipal in
/-- The generator of an ideal of nonzero norm is nonzero. -/
theorem generator_ne_zero_of_absNorm_ne_zero {I : Ideal (𝓞 K)} (hI : absNorm I ≠ 0) :
    generator I ≠ 0 := by
  intro h
  apply hI
  rw [absNorm_eq_zero_iff, (eq_bot_iff_generator_eq_zero I).mpr h]

/-- `|N(u)| = 1` for a unit `u`. -/
theorem natAbs_norm_unit (u : (𝓞 K)ˣ) : (Algebra.norm ℤ (u : 𝓞 K)).natAbs = 1 :=
  Int.isUnit_iff_natAbs_eq.mp (u.isUnit.map (Algebra.norm ℤ))

open Submodule.IsPrincipal in
/-- **The 2-to-1 map, as an equivalence.** For `n ≠ 0`,
`(𝓞 K)ˣ × {I : N(I) = n} ≃ {z ≠ 0 : |N(z)| = n}`, `(u, I) ↦ u · gen(I)`, inverse `z ↦ (unitOf z, (z))`. -/
noncomputable def unitsProdEquiv {n : ℕ} (hn : n ≠ 0) :
    (𝓞 K)ˣ × {I : Ideal (𝓞 K) // absNorm I = n} ≃
      {z : 𝓞 K // z ≠ 0 ∧ (Algebra.norm ℤ z).natAbs = n} where
  toFun p := ⟨(p.1 : 𝓞 K) * generator p.2.1, by
    have hg : generator p.2.1 ≠ 0 := generator_ne_zero_of_absNorm_ne_zero (by rw [p.2.2]; exact hn)
    refine ⟨mul_ne_zero p.1.ne_zero hg, ?_⟩
    rw [map_mul, Int.natAbs_mul, natAbs_norm_unit, one_mul, natAbs_norm_eq_absNorm_span,
      Ideal.span_singleton_generator, p.2.2]⟩
  invFun z := (unitOf z.1, ⟨span {z.1}, by rw [← natAbs_norm_eq_absNorm_span, z.2.2]⟩)
  left_inv p := by
    obtain ⟨u, I, hI⟩ := p
    have hg : generator I ≠ 0 := generator_ne_zero_of_absNorm_ne_zero (by rw [hI]; exact hn)
    have hspan : span {(u : 𝓞 K) * generator I} = I := by
      rw [Ideal.span_singleton_mul_left_unit u.isUnit, Ideal.span_singleton_generator]
    have hspec := unitOf_spec ((u : 𝓞 K) * generator I)
    rw [generator_congr hspan] at hspec
    refine Prod.ext (Units.ext ?_) (Subtype.ext hspan)
    exact mul_right_cancel₀ hg hspec
  right_inv z := Subtype.ext (unitOf_spec z.1)

end PID

include hα hK hm in
/-- **The units are exactly `±1`** (`m ∉ {1, 3}`): `#(𝓞 K)ˣ = 2`. -/
theorem card_units_eq_two (hm1 : m ≠ 1) (hm3 : m ≠ 3) : Nat.card (𝓞 K)ˣ = 2 := by
  rw [Nat.card_eq_two_iff' (1 : (𝓞 K)ˣ)]
  refine ⟨-1, ?_, fun y hy => ?_⟩
  · intro h
    have h' : ((-1 : (𝓞 K)ˣ) : 𝓞 K) = 1 := by rw [h, Units.val_one]
    rw [Units.val_neg, Units.val_one] at h'
    have : (2 : 𝓞 K) = 0 := by linear_combination -h'
    exact two_ne_zero this
  · rcases coe_unit_eq_one_or_neg_one hα hK hm hm1 hm3 y with h | h
    · exact absurd (Units.ext (by rw [h, Units.val_one])) hy
    · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])

include hα hK hm in
/-- **The fibre count.** With every ideal principal and `m ∉ {1, 3}`, for `n ≠ 0`:
`#{z ≠ 0 : |N(z)| = n} = 2 · #{I : N(I) = n}`. -/
theorem card_nonzero_normNat_eq [IsPrincipalIdealRing (𝓞 K)] (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    {n : ℕ} (hn : n ≠ 0) :
    Nat.card {z : 𝓞 K // z ≠ 0 ∧ (Algebra.norm ℤ z).natAbs = n} =
      2 * Nat.card {I : Ideal (𝓞 K) // absNorm I = n} := by
  rw [← Nat.card_congr (unitsProdEquiv hn), Nat.card_prod, card_units_eq_two hα hK hm hm1 hm3]

/-! ### Regrouping the lattice sum by the norm -/

include hα hK hm in
/-- **`Σ′ Q(x,y)^{-s} = 2 Σ_n a_K(n) n^{-s}`** for `Re s > 1`, when every ideal is principal and
`m ∉ {1, 3}`. -/
theorem latticeSum_eq_two_mul_LSeries [IsPrincipalIdealRing (𝓞 K)] (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    {s : ℂ} (hs : 1 < s.re) :
    ∑' v : ℤ × ℤ, ((principalForm m v.1 v.2 : ℤ) : ℂ) ^ (-s) = 2 * LSeries (idealCount K) s := by
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hs; linarith
  -- the summand on `𝓞 K`
  set F : 𝓞 K → ℂ := fun z => ((Algebra.norm ℤ z : ℤ) : ℂ) ^ (-s) with hF
  have hFe : ∀ v : ℤ × ℤ, ((principalForm m v.1 v.2 : ℤ) : ℂ) ^ (-s) = F (intPairEquiv hα hK hm v) := by
    intro v
    simp only [hF, norm_intPairEquiv hα hK hm v]
  have hsumQ : Summable (fun v : ℤ × ℤ => ((principalForm m v.1 v.2 : ℤ) : ℂ) ^ (-s)) :=
    summable_principalForm_cpow hm.ne_zero hs
  have hsumF : Summable F := by
    rw [← (intPairEquiv hα hK hm).summable_iff]
    exact hsumQ.congr hFe
  -- Step A: reindex by `ℤ² ≃ 𝓞 K`
  have hA : ∑' v : ℤ × ℤ, ((principalForm m v.1 v.2 : ℤ) : ℂ) ^ (-s) = ∑' z : 𝓞 K, F z := by
    rw [← (intPairEquiv hα hK hm).tsum_eq F]
    exact tsum_congr hFe
  -- Step B: drop `z = 0` (its term is `0 ^ (-s) = 0`)
  set S : Set (𝓞 K) := {z | z ≠ 0} with hS
  have hF0 : F 0 = 0 := by simp [hF, Complex.zero_cpow hs0]
  have hB : ∑' z : 𝓞 K, F z = ∑' z : S, F z := by
    symm
    apply tsum_subtype_eq_of_support_subset
    intro z hz h0
    exact hz (by rw [h0, hF0])
  -- Step C: regroup along `z ↦ |N(z)|`
  let g : S → ℕ := fun z => (Algebra.norm ℤ z.1).natAbs
  have hC : HasSum (fun n : ℕ => ∑' b : g ⁻¹' {n}, F b.1.1) (∑' z : S, F z) :=
    (hsumF.subtype S).hasSum.tsum_fiberwise g
  -- Step D: the `n`-th fibre sum is `2 · term a_K s n`
  have hD : ∀ n : ℕ, ∑' b : g ⁻¹' {n}, F b.1.1 = 2 * LSeries.term (idealCount K) s n := by
    intro n
    -- the fibre as a subtype of `𝓞 K`
    let e : g ⁻¹' {n} ≃ {z : 𝓞 K // z ≠ 0 ∧ (Algebra.norm ℤ z).natAbs = n} :=
      ⟨fun b => ⟨b.1.1, b.1.2, b.2⟩, fun z => ⟨⟨z.1, z.2.1⟩, z.2.2⟩, fun _ => rfl, fun _ => rfl⟩
    have hconst : ∀ b : g ⁻¹' {n}, F b.1.1 = (n : ℂ) ^ (-s) := by
      intro b
      have hb : (Algebra.norm ℤ b.1.1).natAbs = n := b.2
      simp only [hF]
      rw [norm_cast_eq_natAbs_cast hα hK hm, hb]
    rw [tsum_congr hconst, tsum_const, Nat.card_congr e]
    rcases eq_or_ne n 0 with rfl | hn
    · haveI : IsEmpty {z : 𝓞 K // z ≠ 0 ∧ (Algebra.norm ℤ z).natAbs = 0} :=
        ⟨fun z => z.2.1 ((natAbs_norm_eq_zero_iff z.1).mp z.2.2)⟩
      rw [Nat.card_of_isEmpty, zero_smul, LSeries.term_zero, mul_zero]
    · rw [card_nonzero_normNat_eq hα hK hm hm1 hm3 hn, LSeries.term_of_ne_zero hn,
        idealCount_apply K hn, nsmul_eq_mul, Nat.cast_mul, Complex.cpow_neg, div_eq_mul_inv]
      push_cast
      ring
  -- Step E: assemble
  rw [hA, hB, ← hC.tsum_eq, tsum_congr hD, tsum_mul_left]
  rfl

include hα hK hm in
/-- **Step 1 of the argument.** If `classNumber K = 1` (and `m ∉ {1, 3}`), then for `Re s > 1`
`ζ_K(s) = ½ Σ_{(x,y) ∈ ℤ²} Q(x,y)^{-s}`, where the `(0,0)` term is `0 ^ (-s) = 0`. -/
theorem dedekindZeta_eq_half_latticeSum (hm1 : m ≠ 1) (hm3 : m ≠ 3) (h1 : classNumber K = 1)
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = (1 / 2) * ∑' v : ℤ × ℤ, ((principalForm m v.1 v.2 : ℤ) : ℂ) ^ (-s) := by
  haveI : IsPrincipalIdealRing (𝓞 K) := classNumber_eq_one_iff.mp h1
  rw [latticeSum_eq_two_mul_LSeries hα hK hm hm1 hm3 hs, dedekindZeta_eq_LSeries_idealCount]
  ring

end Field

end CN1.Epstein
