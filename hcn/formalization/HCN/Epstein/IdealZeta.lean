import Mathlib

/-!
# HCN.Epstein.IdealZeta: `ζ_K` as a sum over the nonzero integral ideals

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib-only; valid for every number field `K`.

`NumberField.dedekindZeta K` is the `L`-series of `a_K(n) = #{I : N(I) = n}`. On `re s > 1`:

* `lseriesSummable_card`: that `L`-series converges absolutely. The partial sums `Σ_{k ≤ n} a_K(k)` are
  `O(n)` by Mathlib's ideal-count asymptotics (`Ideal.tendsto_norm_le_div_atTop₀`; the regrouping is the
  one in Mathlib's proof of `tendsto_sub_one_mul_dedekindZeta_nhdsGT`), and
  `LSeriesSummable_of_sum_norm_bigO_and_nonneg` applies;
* `hasSum_dedekindZeta`: `Σ_{I ≠ 0} N(I)^{-s} = ζ_K(s)` as a `HasSum` over `(Ideal (𝓞 K))⁰`. The family is
  regrouped along the norm (`Equiv.sigmaFiberEquiv`); the fibres are finite and the `n`-th one
  contributes the `n`-th `L`-series term (`tsum_fiber_eq_term`).

This is the input to `dedekindZeta_eq_sum_classes` (HCN/Statements/ClassPartition.lean), which then
regroups along `ClassGroup.mk0`.
-/

set_option autoImplicit false

open NumberField Ideal Filter Asymptotics
open scoped nonZeroDivisors Topology

namespace HCN.Epstein

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- `Σ_{k ≤ n} a_K(k) / n` converges (Mathlib's ideal-count asymptotics, as in the residue proof). -/
theorem tendsto_sum_card_div :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℝ)) /
      (n : ℝ)) atTop
      (𝓝 ((2 ^ InfinitePlace.nrRealPlaces K * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K *
        Units.regulator K * classNumber K) /
          (Units.torsionOrder K * Real.sqrt |discr K|))) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

variable (K) in
/-- The `L`-series of `a_K` converges absolutely on `re s > 1`. -/
theorem lseriesSummable_card {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℝ))
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.congr' (((tendsto_sum_card_div K).isBigO_one ℝ).mul
      (isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)) ?_ ?_
    · filter_upwards [eventually_ne_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp
    · filter_upwards with n
      simp
  have := LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun n ↦ Nat.cast_nonneg _) zero_le_one hs
  convert this using 2

/-- The nonzero ideals of norm `n ≠ 0` are the ideals of norm `n`. -/
theorem card_nonZeroDivisors_absNorm_eq {n : ℕ} (hn : n ≠ 0) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} =
      Nat.card {I : Ideal (𝓞 K) // absNorm I = n} := by
  refine Nat.card_congr
    { toFun := fun I => ⟨I.1.1, I.2⟩
      invFun := fun J => ⟨⟨J.1, mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hn ?_⟩, J.2⟩
      left_inv := fun I => rfl
      right_inv := fun J => rfl }
  rw [← J.2, h, Submodule.zero_eq_bot, absNorm_bot]

/-- Finitely many nonzero ideals have a given norm. -/
instance finite_nonZeroDivisors_absNorm_eq (n : ℕ) :
    Finite {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n} := by
  have : Finite {I : Ideal (𝓞 K) // absNorm I = n} := (finite_setOfPred_absNorm_eq n).to_subtype
  exact Finite.of_injective (fun I => (⟨I.1.1, I.2⟩ : {I : Ideal (𝓞 K) // absNorm I = n}))
    fun I J h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')

/-- The `n`-th fibre of the norm on nonzero ideals contributes the `n`-th `L`-series term. -/
theorem tsum_fiber_eq_term (s : ℂ) (n : ℕ) :
    ∑' _ : {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n}, (n : ℂ) ^ (-s) =
      LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s n := by
  rw [tsum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · have : IsEmpty {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = 0} :=
      ⟨fun I => absNorm_ne_zero_of_nonZeroDivisors I.1 I.2⟩
    rw [Nat.card_of_isEmpty, zero_smul, LSeries.term_zero]
  · rw [card_nonZeroDivisors_absNorm_eq hn, LSeries.term_of_ne_zero hn, nsmul_eq_mul,
      Complex.cpow_neg, div_eq_mul_inv]

/-- **`ζ_K(s) = Σ_{I ≠ 0} N(I)^{-s}`** as a `HasSum` over the nonzero integral ideals, on `re s > 1`. -/
theorem hasSum_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ => ((absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      (dedekindZeta K s) := by
  set F : (Ideal (𝓞 K))⁰ → ℂ := fun I => ((absNorm (I : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) with hF
  set a : ℕ → ℂ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ) with ha
  let e := Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 K))⁰ => absNorm (I : Ideal (𝓞 K)))
  have hG : ∀ x, (F ∘ e) x = (x.1 : ℂ) ^ (-s) := by
    rintro ⟨n, I⟩
    simp only [Function.comp_apply, e, Equiv.sigmaFiberEquiv_apply, hF]
    rw [I.2]
  have hL := lseriesSummable_card K hs
  -- summability over the sigma type, via norms
  have hnorm : Summable (fun x => ‖(F ∘ e) x‖) := by
    rw [summable_sigma_of_nonneg (fun x => norm_nonneg _)]
    refine ⟨fun n => Summable.of_finite, ?_⟩
    refine hL.norm.congr fun n => ?_
    simp only [hG]
    rw [← tsum_fiber_eq_term s n, tsum_const, tsum_const, nsmul_eq_mul, nsmul_eq_mul, norm_mul,
      Complex.norm_natCast]
  have hsum : Summable (F ∘ e) := hnorm.of_norm
  have h1 := hsum.hasSum.sigma (fun n => (Summable.of_finite).hasSum)
  have h2 : (fun n => ∑' c : {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n}, (F ∘ e) ⟨n, c⟩) =
      LSeries.term a s := by
    funext n
    simp only [hG]
    exact tsum_fiber_eq_term s n
  rw [h2] at h1
  have h3 : ∑' x, (F ∘ e) x = dedekindZeta K s := by
    rw [h1.unique hL.hasSum]
    rfl
  rw [← e.hasSum_iff, ← h3]
  exact hsum.hasSum

end HCN.Epstein
