import HCN.Statements.GeneralCS
import CN1.Foundations.Basic
import CN1.Epstein.IdealCount
import CN1.Finite.Params
import CN1.Foundations.Discr
import CN1.Finite.Converse
import CN1.Epstein.Lattice
import HCN.Epstein.IdealZeta

/-!
# HCN.Statements.ClassPartition: the class partition of `ζ_K`

The class is NAMED and the basis is FIXED. This file fixed six statements before their proofs were written; they are
proved here, with their proof helpers inserted just before them, together with the small algebraic facts below them.

Setting: `K = ℚ(α)`, `α² = -m`, `m` squarefree, `𝓞 K = ℤ[ω]` (CN-1's `omegaInt`, `ω² = tω - c`), with CN-1's
`t = tOf m`, `c = cOf m`, `d = dOf m = 4c - t²` (Finite/Params.lean), so `N(u + vω) = u² + t u v + c v²`.

* **The Hermite basis.** `IsHermite hα J A B C`: `J = ℤ·A ⊕ ℤ·(B + Cω)` as a `ℤ`-module, with `A > 0`, `C > 0`,
  and `A` the least positive rational integer in `J`. Then `N(J) = A·C`, `C ∣ A`, and the form of `J` in this basis,
  `Q_J(x, y) = N(xA + y(B + Cω)) / N(J)`, has the coefficients
  `a = A/C`, `b = (2B + tC)/C`, `c_J = (B² + tBC + cC²)/(AC)`, so `1 ≤ a = N(J/content) ≤ N(J)` and `4 a c_J - b² = d`.
  `exists_isHermite` is the 100-150-line sub-lemma ("J ∩ ℤ = Aℤ, and A extends to a ℤ-basis of J").
* **The class sum, with the class named.** For a nonzero integral `J` with Hermite data `(A, B, C)`, the integral
  ideals in the class `[J]⁻¹` satisfy `Σ_{I : mk0 I = [J]⁻¹} N(I)^{-s} = ½ Z_{Q_J}(s)` (`hasSum_classSum`; the bijection
  is `β ↦ J⁻¹(β)` on `(J \ 0)/{±1}`, so `w = 2` needs `m ∉ {1, 3}`). So the representative used for a class `Cl` lies
  in `Cl⁻¹`.
* **The partition** `ζ_K = Σ_{Cl} Σ_{I ∈ Cl} N(I)^{-s}` over Mathlib's `ClassGroup (𝓞 K)` (a `Fintype`), and the
  assembled form `exists_classReps`: representatives `J_Cl ∈ Cl⁻¹` with Hermite data, `J_1 = ⊤` with `(1, 0, 1)` (so the
  principal class gives CN-1's principal form, `a = 1`), `N(J_Cl) ≤ (2/3)√d` (Minkowski, CN-1's Converse.lean:31), and
  `ζ_K(s) = Σ_{Cl} ½ Z_{Q_{J_Cl}}(s)` on `re s > 1`.

Everything is stated over Mathlib's `ClassGroup.mk0`, `Ideal.absNorm` and `NumberField.dedekindZeta`; no forms
bridge is needed to state it.
-/

set_option autoImplicit false

open NumberField Ideal CN1.Foundations CN1.Finite
open scoped nonZeroDivisors

namespace HCN.Epstein

/-! ### The form of a Hermite basis -/

/-- `a = A / C`, the leading coefficient of `Q_J` in the Hermite basis `(A, B + Cω)`. -/
noncomputable def formA (A C : ℤ) : ℝ := (A : ℝ) / C

/-- `b = (2B + tC) / C`. -/
noncomputable def formB (m : ℕ) (B C : ℤ) : ℝ := (2 * (B : ℝ) + tOf m * C) / C

/-- `c_J = (B² + tBC + cC²) / (AC)`. -/
noncomputable def formC (m : ℕ) (A B C : ℤ) : ℝ :=
  ((B : ℝ) ^ 2 + tOf m * B * C + cOf m * (C : ℝ) ^ 2) / (A * C)

/-- The discriminant of `Q_J` is `d = dOf m`, for any `A, C ≠ 0` (no integrality needed). -/
theorem disc_form (m : ℕ) {A B C : ℤ} (hA : A ≠ 0) (hC : C ≠ 0) :
    HCN.CS.disc (formA A C) (formB m B C) (formC m A B C) = dOf m := by
  have h4 : (4 * cOf m : ℝ) = dOf m + (tOf m : ℝ) ^ 2 := by exact_mod_cast four_mul_cOf m
  have hA' : (A : ℝ) ≠ 0 := by exact_mod_cast hA
  have hC' : (C : ℝ) ≠ 0 := by exact_mod_cast hC
  unfold HCN.CS.disc formA formB formC
  field_simp
  linear_combination (C : ℝ) ^ 2 * h4

/-- At `(A, B, C) = (1, 0, 1)` the form is CN-1's principal form `(1, bq d, cq d)`. -/
theorem form_one_zero_one (m : ℕ) :
    formA 1 1 = 1 ∧ formB m 0 1 = CN1.CS.bq (dOf m) ∧ formC m 1 0 1 = CN1.CS.cq (dOf m) := by
  refine ⟨by simp [formA], ?_, ?_⟩
  · unfold formB CN1.CS.bq tOf dOf
    split_ifs with h
    · have e : m % 2 = 1 := by omega
      rw [e]; norm_num
    · have e : 4 * m % 2 = 0 := by omega
      rw [e]; norm_num
  · unfold formC CN1.CS.cq cOf dOf tOf
    split_ifs with h
    · have e : (m + m % 2) / 4 = (m + 1) / 4 := by omega
      rw [e]; norm_num
    · have e : (4 * m + 4 * m % 2) / 4 = m := by omega
      rw [e]; norm_num

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K}

/-- **Hermite basis data** of an integral ideal `J` of `𝓞 K = ℤ[ω]`: `J = ℤ·A ⊕ ℤ·(B + Cω)` as a `ℤ`-submodule, with
`A, C > 0` and `A` the least positive rational integer in `J`. -/
structure IsHermite (hα : α ^ 2 = -(m : K)) (J : Ideal (𝓞 K)) (A B C : ℤ) : Prop where
  A_pos : 0 < A
  C_pos : 0 < C
  span_eq : J.restrictScalars ℤ =
    Submodule.span ℤ {((A : ℤ) : 𝓞 K), ((B : ℤ) : 𝓞 K) + ((C : ℤ) : 𝓞 K) * omegaInt hα}
  A_least : ∀ n : ℤ, 0 < n → ((n : ℤ) : 𝓞 K) ∈ J → A ≤ n

variable (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2) (hm : Squarefree m)

/-! ### Proof helpers for the Hermite sub-lemma -/

/-- `x • A + y • (B + Cω) = (xA + yB) + (yC)ω`. -/
theorem zsmul_hermite_pair (A B C x y : ℤ) :
    x • ((A : ℤ) : 𝓞 K) + y • (((B : ℤ) : 𝓞 K) + ((C : ℤ) : 𝓞 K) * omegaInt hα) =
      ((x * A + y * B : ℤ) : 𝓞 K) + ((y * C : ℤ) : 𝓞 K) * omegaInt hα := by
  simp only [zsmul_eq_mul]; push_cast; ring

/-- Membership in a Hermite ideal: `z ∈ J ↔ z = xA + y(B + Cω)` for some `x, y : ℤ`. -/
theorem IsHermite.mem_iff {J : Ideal (𝓞 K)} {A B C : ℤ} (h : IsHermite hα J A B C) {z : 𝓞 K} :
    z ∈ J ↔ ∃ x y : ℤ, z = ((x * A + y * B : ℤ) : 𝓞 K) + ((y * C : ℤ) : 𝓞 K) * omegaInt hα := by
  have : z ∈ J ↔ z ∈ J.restrictScalars ℤ := Iff.rfl
  rw [this, h.span_eq, Submodule.mem_span_pair]
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨x, y, by rw [← hxy, zsmul_hermite_pair]⟩
  · rintro ⟨x, y, hxy⟩
    exact ⟨x, y, by rw [hxy, zsmul_hermite_pair]⟩

include hK hm in
/-- The coordinates of `u + wω` in the integral basis `{1, ω}`. -/
theorem repr_intBasis (u w : ℤ) :
    ⇑((intBasis hα hK hm).repr ((u : 𝓞 K) + (w : 𝓞 K) * omegaInt hα)) = ![u, w] := by
  have e : ((u : 𝓞 K) + (w : 𝓞 K) * omegaInt hα) = ∑ i, (![u, w] i) • intBasis hα hK hm i := by
    simp [Fin.sum_univ_two, zsmul_eq_mul]
  rw [e, Module.Basis.repr_sum_self]

/-! ### The Hermite sub-lemma -/

include hK hm in
/-- **Every nonzero integral ideal has a Hermite basis.** -/
theorem exists_isHermite {J : Ideal (𝓞 K)} (hJ : J ≠ ⊥) : ∃ A B C : ℤ, IsHermite hα J A B C := by
  classical
  -- `A` is the least positive integer in `J`; `C` the least positive `ω`-coordinate of an element of `J`
  have hN0 : absNorm J ≠ 0 := by rwa [Ne, absNorm_eq_zero_iff]
  have hexA : ∃ n : ℕ, 0 < n ∧ ((n : ℤ) : 𝓞 K) ∈ J :=
    ⟨absNorm J, Nat.pos_of_ne_zero hN0, by exact_mod_cast absNorm_mem J⟩
  obtain ⟨ha0, haJ⟩ := Nat.find_spec hexA
  have ha_min : ∀ n : ℕ, n < Nat.find hexA → ¬ (0 < n ∧ ((n : ℤ) : 𝓞 K) ∈ J) :=
    fun n hn => Nat.find_min hexA hn
  set a := Nat.find hexA with ha_def
  have hexC : ∃ n : ℕ, 0 < n ∧ ∃ u : ℤ, (u : 𝓞 K) + ((n : ℤ) : 𝓞 K) * omegaInt hα ∈ J :=
    ⟨a, ha0, 0, by simpa using J.mul_mem_right (omegaInt hα) haJ⟩
  obtain ⟨hc0, B, hB⟩ := Nat.find_spec hexC
  have hc_min : ∀ n : ℕ, n < Nat.find hexC →
      ¬ (0 < n ∧ ∃ u : ℤ, (u : 𝓞 K) + ((n : ℤ) : 𝓞 K) * omegaInt hα ∈ J) :=
    fun n hn => Nat.find_min hexC hn
  set c := Nat.find hexC with hc_def
  -- `J ∩ ℤ = aℤ`
  have hdivA : ∀ n : ℤ, (n : 𝓞 K) ∈ J → (a : ℤ) ∣ n := by
    intro n hn
    have ha' : (0 : ℤ) < a := by exact_mod_cast ha0
    have hr : ((n % (a : ℤ) : ℤ) : 𝓞 K) ∈ J := by
      have e : n % (a : ℤ) = n - (n / a) * a := by rw [Int.emod_def]; ring
      rw [e]; push_cast
      exact J.sub_mem hn (J.mul_mem_left _ (by exact_mod_cast haJ))
    have h0 : 0 ≤ n % (a : ℤ) := Int.emod_nonneg _ ha'.ne'
    have h1 : n % (a : ℤ) < a := Int.emod_lt_of_pos _ ha'
    by_contra hnd
    have hpos : 0 < n % (a : ℤ) :=
      lt_of_le_of_ne h0 (fun h => hnd (Int.dvd_of_emod_eq_zero h.symm))
    apply ha_min (n % (a : ℤ)).toNat (by omega)
    refine ⟨by omega, ?_⟩
    rwa [Int.toNat_of_nonneg h0]
  -- the `ω`-coordinates of `J` are `cℤ`
  have hdivC : ∀ u v : ℤ, (u : 𝓞 K) + (v : 𝓞 K) * omegaInt hα ∈ J → (c : ℤ) ∣ v := by
    intro u v huv
    have hc' : (0 : ℤ) < c := by exact_mod_cast hc0
    have hr : (((u - (v / c) * B : ℤ) : 𝓞 K) + ((v % (c : ℤ) : ℤ) : 𝓞 K) * omegaInt hα) ∈ J := by
      have e : v % (c : ℤ) = v - (v / c) * c := by rw [Int.emod_def]; ring
      have := J.sub_mem huv (J.mul_mem_left ((v / c : ℤ) : 𝓞 K) hB)
      convert this using 1
      rw [e]; push_cast; ring
    have h0 : 0 ≤ v % (c : ℤ) := Int.emod_nonneg _ hc'.ne'
    have h1 : v % (c : ℤ) < c := Int.emod_lt_of_pos _ hc'
    by_contra hnd
    have hpos : 0 < v % (c : ℤ) :=
      lt_of_le_of_ne h0 (fun h => hnd (Int.dvd_of_emod_eq_zero h.symm))
    apply hc_min (v % (c : ℤ)).toNat (by omega)
    refine ⟨by omega, u - (v / c) * B, ?_⟩
    rwa [Int.toNat_of_nonneg h0]
  refine ⟨a, B, c, ⟨by exact_mod_cast ha0, by exact_mod_cast hc0, ?_, ?_⟩⟩
  · apply le_antisymm
    · -- `u + vω ∈ J`: `v = qc`, then `u - qB ∈ J ∩ ℤ` is `ra`
      intro z hz
      obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
      obtain ⟨q, hq⟩ := hdivC u v hz
      have hz' : ((u - q * B : ℤ) : 𝓞 K) ∈ J := by
        have := J.sub_mem hz (J.mul_mem_left (q : 𝓞 K) hB)
        convert this using 1
        rw [hq]; push_cast; ring
      obtain ⟨r, hr⟩ := hdivA _ hz'
      rw [Submodule.mem_span_pair]
      refine ⟨r, q, ?_⟩
      rw [zsmul_hermite_pair]
      have hu : u = r * a + q * B := by linarith [hr]
      rw [hu, hq]
      push_cast; ring
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact haJ
      · exact hB
  · intro n hn hnJ
    obtain ⟨k, hk⟩ := hdivA n hnJ
    exact Int.le_of_dvd hn ⟨k, hk⟩

include hK hm in
/-- **`N(J) = A·C`** for a Hermite basis (`natAbs_det_basis_change` against `intBasis`). -/
theorem IsHermite.absNorm_eq {J : Ideal (𝓞 K)} {A B C : ℤ} (h : IsHermite hα J A B C) :
    (absNorm J : ℤ) = A * C := by
  classical
  set v : Fin 2 → 𝓞 K := ![((A : ℤ) : 𝓞 K), ((B : ℤ) : 𝓞 K) + ((C : ℤ) : 𝓞 K) * omegaInt hα] with hv
  have hli : LinearIndependent ℤ v := by
    rw [LinearIndependent.pair_iff]
    intro x y hxy
    rw [zsmul_hermite_pair] at hxy
    have e0 : (0 : 𝓞 K) = ((0 : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * omegaInt hα := by simp
    rw [e0] at hxy
    obtain ⟨h1, h2⟩ := int_add_int_mul_omegaInt_inj hα hK hm.ne_zero hxy
    have hy : y = 0 := by
      rcases mul_eq_zero.mp h2 with h' | h'
      · exact h'
      · exact absurd h' h.C_pos.ne'
    subst hy
    refine ⟨?_, rfl⟩
    rcases mul_eq_zero.mp (by simpa using h1 : x * A = 0) with h' | h'
    · exact h'
    · exact absurd h' h.A_pos.ne'
  have hr : Set.range v = {((A : ℤ) : 𝓞 K), ((B : ℤ) : 𝓞 K) + ((C : ℤ) : 𝓞 K) * omegaInt hα} := by
    rw [hv, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  have hspan : Submodule.span ℤ (Set.range v) = J.restrictScalars ℤ := by rw [hr, h.span_eq]
  -- the basis `(A, B + Cω)` of `J`, and `N(J) = |det| = AC` against `{1, ω}`
  let bJ : Module.Basis (Fin 2) ℤ (J.restrictScalars ℤ) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan)
  have hbJ : ((↑) ∘ bJ : Fin 2 → 𝓞 K) = v := by
    funext i
    simp [bJ, Module.Basis.span_apply]
  have key : ((intBasis hα hK hm).det v).natAbs = absNorm J :=
    (congrArg (fun w => ((intBasis hα hK hm).det w).natAbs) hbJ).symm.trans
      (natAbs_det_basis_change (intBasis hα hK hm) J bJ)
  have hdet : (intBasis hα hK hm).det v = A * C := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    simp only [Module.Basis.toMatrix_apply]
    have h0 : v 0 = ((A : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * omegaInt hα := by simp [hv]
    have h1 : v 1 = ((B : ℤ) : 𝓞 K) + ((C : ℤ) : 𝓞 K) * omegaInt hα := by simp [hv]
    rw [h0, h1, repr_intBasis, repr_intBasis]
    simp
  rw [hdet] at key
  rw [← key, Int.natCast_natAbs, abs_of_pos (mul_pos h.A_pos h.C_pos)]

include hK hm in
/-- **`C ∣ A`**, so `a = A/C` is a positive integer (from `N(J) = AC ∣ N(A) = A²`). -/
theorem IsHermite.C_dvd_A {J : Ideal (𝓞 K)} {A B C : ℤ} (h : IsHermite hα J A B C) : C ∣ A := by
  -- `Aω ∈ J` is `xA + y(B + Cω)`, so `yC = A`
  have hA : ((A : ℤ) : 𝓞 K) ∈ J := (IsHermite.mem_iff hα h).mpr ⟨1, 0, by simp⟩
  obtain ⟨x, y, hxy⟩ := (IsHermite.mem_iff hα h).mp (J.mul_mem_right (omegaInt hα) hA)
  have e : ((A : ℤ) : 𝓞 K) * omegaInt hα = ((0 : ℤ) : 𝓞 K) + ((A : ℤ) : 𝓞 K) * omegaInt hα := by simp
  rw [e] at hxy
  have := (int_add_int_mul_omegaInt_inj hα hK hm.ne_zero hxy).2
  exact ⟨y, by rw [this]; ring⟩

/-! ### Consequences proved here -/

include hK hm in
/-- `1 ≤ a`. -/
theorem IsHermite.one_le_formA {J : Ideal (𝓞 K)} {A B C : ℤ} (h : IsHermite hα J A B C) :
    1 ≤ formA A C := by
  obtain ⟨k, hk⟩ := h.C_dvd_A hα hK hm
  have hC := h.C_pos
  have hk1 : 1 ≤ k := by
    have := h.A_pos
    rw [hk] at this
    by_contra hk1
    push Not at hk1
    nlinarith
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  rw [formA, hk, le_div_iff₀ hC']
  push_cast
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  nlinarith

include hK hm in
/-- `a = N(J/content) ≤ N(J)`. -/
theorem IsHermite.formA_le_absNorm {J : Ideal (𝓞 K)} {A B C : ℤ} (h : IsHermite hα J A B C) :
    formA A C ≤ absNorm J := by
  have hN := h.absNorm_eq hα hK hm
  have hA : (0 : ℝ) < A := by exact_mod_cast h.A_pos
  have hC : (1 : ℝ) ≤ C := by exact_mod_cast h.C_pos
  have hN' : ((absNorm J : ℕ) : ℝ) = A * C := by exact_mod_cast hN
  rw [formA, hN', div_le_iff₀ (by linarith)]
  nlinarith

/-- `principalForm m u v = u² + t u v + c v²`. -/
theorem principalForm_eq_tc (u v : ℤ) :
    principalForm m u v = u ^ 2 + (tOf m : ℤ) * u * v + (cOf m : ℤ) * v ^ 2 := by
  unfold principalForm tOf cOf
  split_ifs <;> push_cast <;> ring

include hK hm in
/-- **The form of `J`:** `N(xA + y(B + Cω)) = N(J) · Q_J(x, y)`, where `xA + y(B + Cω) = (xA + yB) + (yC)ω`. -/
theorem IsHermite.norm_eq {J : Ideal (𝓞 K)} {A B C : ℤ} (h : IsHermite hα J A B C) (x y : ℤ) :
    ((Algebra.norm ℤ (((x * A + y * B : ℤ) : 𝓞 K) + ((y * C : ℤ) : 𝓞 K) * omegaInt hα) : ℤ) : ℝ) =
      (absNorm J : ℝ) * HCN.CS.Qg (formA A C) (formB m B C) (formC m A B C) x y := by
  have hN : ((absNorm J : ℕ) : ℝ) = A * C := by exact_mod_cast h.absNorm_eq hα hK hm
  have hA : (A : ℝ) ≠ 0 := by exact_mod_cast h.A_pos.ne'
  have hC : (C : ℝ) ≠ 0 := by exact_mod_cast h.C_pos.ne'
  rw [norm_int_eq_principalForm hα hK hm.ne_zero rfl, principalForm_eq_tc, hN]
  unfold HCN.CS.Qg formA formB formC
  push_cast
  field_simp
  ring

include hK hm in
/-- Non-vacuity: `⊤ = ℤ·1 ⊕ ℤ·ω` is Hermite with `(1, 0, 1)`. -/
theorem isHermite_top : IsHermite hα (⊤ : Ideal (𝓞 K)) 1 0 1 := by
  refine ⟨one_pos, one_pos, ?_, fun n hn _ => hn⟩
  have hb := (intBasis hα hK hm).span_eq
  have hr : Set.range (intBasis hα hK hm) = {(1 : 𝓞 K), omegaInt hα} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      exacts [⟨0, by simp⟩, ⟨1, by simp⟩]
  rw [hr] at hb
  simp only [Int.cast_one, Int.cast_zero, zero_add, one_mul]
  rw [hb, Submodule.restrictScalars_top]

/-! ### The class sum and the partition -/

include hK hm in
/-- **The class sum, with the class named.** For a nonzero integral ideal `J` with Hermite data `(A, B, C)` and
`m ∉ {1, 3}`: `Σ_{I integral, mk0 I = [J]⁻¹} N(I)^{-s} = ½ Z_{Q_J}(s)` on `re s > 1`, with
`Q_J = (A/C, (2B + tC)/C, (B² + tBC + cC²)/(AC))`. -/
theorem hasSum_classSum (hm1 : m ≠ 1) (hm3 : m ≠ 3) (J : (Ideal (𝓞 K))⁰) {A B C : ℤ}
    (hH : IsHermite hα (J : Ideal (𝓞 K)) A B C) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹} =>
        ((absNorm (I.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s))
      ((1 / 2 : ℂ) * HCN.CS.Zg (formA A C) (formB m B C) (formC m A B C) s) := by
  classical
  set Q : ℤ → ℤ → ℝ := HCN.CS.Qg (formA A C) (formB m B C) (formC m A B C) with hQdef
  set N : ℕ := absNorm (J : Ideal (𝓞 K)) with hNdef
  have hNpos : 0 < N := Nat.pos_of_ne_zero (absNorm_ne_zero_of_nonZeroDivisors J)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hs; linarith
  -- the lattice points of `J`
  let β : ℤ × ℤ → 𝓞 K := fun v =>
    ((v.1 * A + v.2 * B : ℤ) : 𝓞 K) + ((v.2 * C : ℤ) : 𝓞 K) * omegaInt hα
  have hβmem : ∀ v, β v ∈ (J : Ideal (𝓞 K)) := fun v =>
    (IsHermite.mem_iff hα hH).mpr ⟨v.1, v.2, rfl⟩
  have hβinj : ∀ v w, β v = β w → v = w := by
    intro v w h
    obtain ⟨h1, h2⟩ := int_add_int_mul_omegaInt_inj hα hK hm.ne_zero h
    have e2 : v.2 = w.2 := mul_right_cancel₀ hH.C_pos.ne' h2
    have e1 : v.1 = w.1 := by
      rw [e2] at h1
      exact mul_right_cancel₀ hH.A_pos.ne' (by linarith)
    exact Prod.ext e1 e2
  have hβneg : ∀ v, β (-v) = -β v := by
    intro v
    simp only [β, Prod.fst_neg, Prod.snd_neg]
    push_cast; ring
  have hβ0 : β 0 = 0 := by simp [β]
  have hβne : ∀ v, v ≠ 0 → β v ≠ 0 := fun v hv h => hv (hβinj v 0 (h.trans hβ0.symm))
  -- the norm of a lattice point is `N(J) · Q_J`
  have hnormβ : ∀ v : ℤ × ℤ, ((Algebra.norm ℤ (β v) : ℤ) : ℝ) = (N : ℝ) * Q v.1 v.2 :=
    fun v => hH.norm_eq hα hK hm v.1 v.2
  have hQform : ∀ v : ℤ × ℤ,
      Q v.1 v.2 = ((principalForm m (v.1 * A + v.2 * B) (v.2 * C) : ℤ) : ℝ) / N := by
    intro v
    have h := hnormβ v
    rw [norm_int_eq_principalForm hα hK hm.ne_zero rfl] at h
    rw [h]
    field_simp
  have hQnn : ∀ v : ℤ × ℤ, 0 ≤ Q v.1 v.2 := by
    intro v
    rw [hQform v]
    exact div_nonneg (by exact_mod_cast principalForm_nonneg m _ _) hNR.le
  -- summability of the lattice sum
  set f : ℤ × ℤ → ℂ := fun v => ((Q v.1 v.2 : ℝ) : ℂ) ^ (-s) with hf
  let L : ℤ × ℤ → ℤ × ℤ := fun v => (v.1 * A + v.2 * B, v.2 * C)
  have hLinj : Function.Injective L := by
    intro v w h
    apply hβinj
    simp only [L, Prod.mk.injEq] at h
    simp only [β, h.1, h.2]
  have hsumf : Summable f := by
    have hg := ((CN1.Epstein.summable_principalForm_rpow hm.ne_zero hs).comp_injective
      hLinj).mul_left ((N : ℝ) ^ s.re)
    refine Summable.of_norm_bounded hg fun v => le_of_eq ?_
    simp only [hf, Function.comp_apply, L]
    rw [Complex.norm_cpow_eq_rpow_re_of_nonneg (hQnn v) (by rw [Complex.neg_re]; linarith),
      Complex.neg_re, hQform v, Real.div_rpow (by exact_mod_cast principalForm_nonneg m _ _)
        hNR.le, Real.rpow_neg hNR.le, div_inv_eq_mul, mul_comm]
  have hf0 : f 0 = 0 := by
    simp only [hf, Prod.fst_zero, Prod.snd_zero, hQdef, HCN.CS.Qg]
    simp [Complex.zero_cpow hs0]
  -- the integral ideal `I` with `J I = (β)`, which lies in `[J]⁻¹`
  set S : Set (ℤ × ℤ) := {v | v ≠ 0} with hS
  set T := {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹}
  have hJne : (J : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  have hex : ∀ v : S, ∃ I : T, (J : Ideal (𝓞 K)) * ((I.1 : Ideal (𝓞 K))) = span {β v.1} := by
    intro v
    obtain ⟨I0, hI0⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr (hβmem v.1))
    have hI0ne : I0 ≠ 0 := by
      rintro rfl
      rw [mul_zero, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot] at hI0
      exact hβne v.1 v.2 hI0
    refine ⟨⟨⟨I0, mem_nonZeroDivisors_iff_ne_zero.mpr hI0ne⟩, ?_⟩, hI0.symm⟩
    rw [ClassGroup.mk0_eq_mk0_inv_iff]
    refine ⟨β v.1, hβne v.1 v.2, ?_⟩
    rw [mul_comm]
    exact hI0.symm
  choose Φ hΦ using hex
  have hΦeq : ∀ (v : S) (I : T), (J : Ideal (𝓞 K)) * (I.1 : Ideal (𝓞 K)) = span {β v.1} → Φ v = I := by
    intro v I hI
    apply Subtype.ext; apply Subtype.ext
    exact mul_left_cancel₀ hJne ((hΦ v).trans hI.symm)
  have hfiber : ∀ v w : S, Φ v = Φ w ↔ (w.1 = v.1 ∨ w.1 = -v.1) := by
    intro v w
    constructor
    · intro h
      have hsp : span {β v.1} = span {β w.1} := by rw [← hΦ v, ← hΦ w, h]
      obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hsp
      rcases coe_unit_eq_one_or_neg_one hα hK hm hm1 hm3 u with h1 | h1
      · left; apply hβinj; rw [← hu, h1, mul_one]
      · right; apply hβinj; rw [hβneg, ← hu, h1, mul_neg_one]
    · rintro (h | h)
      · exact (hΦeq w (Φ v) (by rw [hΦ v, h])).symm
      · exact (hΦeq w (Φ v) (by rw [hΦ v, h, hβneg, Ideal.span_singleton_neg])).symm
  have hsurj : ∀ I : T, ∃ v : S, Φ v = I := by
    intro I
    obtain ⟨x, hx0, hx⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp I.2
    have hxJ : x ∈ (J : Ideal (𝓞 K)) := by
      have : span {x} ≤ (J : Ideal (𝓞 K)) := by rw [← hx]; exact Ideal.mul_le_right
      exact this (Ideal.mem_span_singleton_self x)
    obtain ⟨a, b, hab⟩ := (IsHermite.mem_iff hα hH).mp hxJ
    have hv : ((a, b) : ℤ × ℤ) ≠ 0 := by
      intro h
      apply hx0
      rw [hab]
      simp only [Prod.mk_eq_zero] at h
      rw [h.1, h.2]; simp
    refine ⟨⟨(a, b), hv⟩, hΦeq _ I ?_⟩
    rw [mul_comm, hx, hab]
  -- the value of a lattice point is the norm of its ideal
  have hval : ∀ v : S, Q v.1.1 v.1.2 = (absNorm ((Φ v).1 : Ideal (𝓞 K)) : ℝ) := by
    intro v
    have h1 := congrArg absNorm (hΦ v)
    rw [map_mul, absNorm_span_singleton] at h1
    have hnn := CN1.Epstein.norm_int_nonneg hα hK hm (β v.1)
    have h3 : (((Algebra.norm ℤ (β v.1)).natAbs : ℕ) : ℝ) = ((Algebra.norm ℤ (β v.1) : ℤ) : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hnn)]
    have h4 : (N : ℝ) * (absNorm ((Φ v).1 : Ideal (𝓞 K)) : ℝ) = (N : ℝ) * Q v.1.1 v.1.2 := by
      rw [← hnormβ v.1, ← h3]
      exact_mod_cast h1
    exact (mul_left_cancel₀ hNR.ne' h4).symm
  -- each fibre has two elements
  have hcard : ∀ I : T, Nat.card ↑(Φ ⁻¹' {I}) = 2 := by
    intro I
    obtain ⟨w, hw⟩ := hsurj I
    have hw' : -w.1 ∈ S := neg_ne_zero.mpr w.2
    have hwI : Φ ⟨-w.1, hw'⟩ = I := ((hfiber w ⟨-w.1, hw'⟩).mpr (Or.inr rfl)).symm.trans hw
    rw [Nat.card_eq_two_iff' (⟨w, hw⟩ : ↑(Φ ⁻¹' {I}))]
    refine ⟨⟨⟨-w.1, hw'⟩, hwI⟩, ?_, ?_⟩
    · intro h
      have h' : -w.1 = w.1 := congrArg (fun b : ↑(Φ ⁻¹' {I}) => b.1.1) h
      apply w.2
      have h1 := congrArg Prod.fst h'
      have h2 := congrArg Prod.snd h'
      simp only [Prod.fst_neg, Prod.snd_neg] at h1 h2
      exact Prod.ext (by simp; omega) (by simp; omega)
    · intro y hy
      have hyw : Φ w = Φ y.1 := hw.trans y.2.symm
      rcases (hfiber w y.1).mp hyw with h | h
      · exact absurd (Subtype.ext (Subtype.ext h)) hy
      · exact Subtype.ext (Subtype.ext h)
  -- regroup
  have hS' : HasSum (fun b : S => f b.1) (∑' v, f v) := by
    have := hsumf.hasSum
    rw [← hasSum_subtype_iff_of_support_subset (s := S)] at this
    · exact this
    · intro v hv h0
      exact hv (by rw [h0, hf0])
  have hF := hS'.tsum_fiberwise Φ
  have hfib : ∀ I : T, ∑' b : ↑(Φ ⁻¹' {I}), f b.1.1 = 2 * ((absNorm (I.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) := by
    intro I
    have hconst : ∀ b : ↑(Φ ⁻¹' {I}), f b.1.1 = ((absNorm (I.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) := by
      intro b
      have hb : Φ b.1 = I := b.2
      simp only [hf]
      rw [hval b.1, hb, Complex.ofReal_natCast]
    rw [tsum_congr hconst, tsum_const, hcard I, two_nsmul, two_mul]
  have hF2 : HasSum (fun I : T => 2 * ((absNorm (I.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s)) (∑' v, f v) := by
    convert hF using 1
    funext I
    exact (hfib I).symm
  have := hF2.mul_left (1 / 2 : ℂ)
  convert this using 1
  · funext I
    ring
  · rfl

/-- **The partition of `ζ_K` over the class group** (any number field), on `re s > 1`. -/
theorem dedekindZeta_eq_sum_classes {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = ∑ Cl : ClassGroup (𝓞 K),
      ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = Cl}, ((absNorm (I.1 : Ideal (𝓞 K)) : ℕ) : ℂ) ^ (-s) := by
  have h := (hasSum_dedekindZeta hs).tsum_fiberwise
    (fun I : (Ideal (𝓞 K))⁰ => ClassGroup.mk0 I)
  rw [← h.tsum_eq, tsum_fintype]
  rfl

include hm in
/-- `1 ≤ (2/3)√d`, since `d = dOf m ≥ 3`: the principal class's `N(⊤) = 1` is in range. -/
theorem one_le_two_thirds_sqrt_dOf : (1 : ℝ) ≤ 2 / 3 * Real.sqrt (dOf m) := by
  have hm0 := hm.ne_zero
  have h3 : (3 : ℝ) ≤ dOf m := by
    have : 3 ≤ dOf m := by unfold dOf; split_ifs <;> omega
    exact_mod_cast this
  have hs : (3 / 2 : ℝ) ≤ Real.sqrt (dOf m) := Real.le_sqrt_of_sq_le (by linarith)
  linarith

include hK hm in
/-- **Assembled: `ζ_K = Σ_Cl ½ Z_{Q_{J_Cl}}`**, with `J_Cl ∈ Cl⁻¹` in Hermite form, the principal class
represented by `⊤` with `(1, 0, 1)`, and `N(J_Cl) ≤ (2/3)√d`. So every `a_Cl = A_Cl/C_Cl` lies in `[1, (2/3)√d]`
(`one_le_formA`, `formA_le_absNorm`), the range of `HCN.CS.Bg_mono`, and the principal class has `a = 1`. -/
theorem exists_classReps (hm1 : m ≠ 1) (hm3 : m ≠ 3) :
    ∃ (J : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰) (A B C : ClassGroup (𝓞 K) → ℤ),
      (∀ Cl, ClassGroup.mk0 (J Cl) = Cl⁻¹) ∧
      (∀ Cl, IsHermite hα (J Cl : Ideal (𝓞 K)) (A Cl) (B Cl) (C Cl)) ∧
      ((J 1 : Ideal (𝓞 K)) = ⊤ ∧ A 1 = 1 ∧ B 1 = 0 ∧ C 1 = 1) ∧
      (∀ Cl, ((absNorm (J Cl : Ideal (𝓞 K)) : ℕ) : ℝ) ≤ 2 / 3 * Real.sqrt (dOf m)) ∧
      ∀ s : ℂ, 1 < s.re → dedekindZeta K s = ∑ Cl : ClassGroup (𝓞 K),
        (1 / 2 : ℂ) * HCN.CS.Zg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) s := by
  have hdisc : |discr K| ≤ (dOf m : ℤ) := by
    rw [discr_eq hα hK hm, abs_neg, Nat.abs_cast]
    exact le_of_eq (by unfold disc dOf; rfl)
  have htop : ((1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = ⊤ := by
    rw [Submonoid.coe_one, Ideal.one_eq_top]
  have hex : ∀ Cl : ClassGroup (𝓞 K), ∃ (J : (Ideal (𝓞 K))⁰) (A B C : ℤ),
      ClassGroup.mk0 J = Cl⁻¹ ∧ IsHermite hα (J : Ideal (𝓞 K)) A B C ∧
      (Cl = 1 → (J : Ideal (𝓞 K)) = ⊤ ∧ A = 1 ∧ B = 0 ∧ C = 1) ∧
      ((absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) ≤ 2 / 3 * Real.sqrt (dOf m) := by
    intro Cl
    by_cases h1 : Cl = 1
    · subst h1
      refine ⟨1, 1, 0, 1, by rw [map_one, inv_one], ?_, fun _ => ⟨htop, rfl, rfl, rfl⟩, ?_⟩
      · rw [htop]
        exact isHermite_top hα hK hm
      · rw [htop, absNorm_top, Nat.cast_one]
        exact one_le_two_thirds_sqrt_dOf hm
    · obtain ⟨J, hJ, hJN⟩ := exists_ideal_in_class_of_norm_le Cl⁻¹
      have hJ0 : (J : Ideal (𝓞 K)) ≠ ⊥ := by
        rw [Ne, ← Submodule.zero_eq_bot]
        exact nonZeroDivisors.coe_ne_zero J
      obtain ⟨A, B, C, hH⟩ := exists_isHermite hα hK hm hJ0
      exact ⟨J, A, B, C, hJ, hH, fun h => absurd h h1, le_two_thirds_sqrt_of_le_minkowski hK hdisc hJN⟩
  choose J A B C hJ hH h1 hN using hex
  refine ⟨J, A, B, C, hJ, hH, h1 1 rfl, hN, fun s hs => ?_⟩
  rw [dedekindZeta_eq_sum_classes hs]
  refine Finset.sum_congr rfl fun Cl _ => ?_
  have hS := hasSum_classSum hα hK hm hm1 hm3 (J Cl) (hH Cl) hs
  have e : (ClassGroup.mk0 (J Cl))⁻¹ = Cl := by rw [hJ Cl, inv_inv]
  rw [e] at hS
  exact hS.tsum_eq

end HCN.Epstein
