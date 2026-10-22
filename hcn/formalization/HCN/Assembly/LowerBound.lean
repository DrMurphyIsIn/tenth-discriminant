import HCN.Statements.ClassPartition
import HCN.Numerics.Threshold
import CN1.Epstein.Factorization
import CN1.Assembly.Positivity
import CN1.ChowlaSelberg.Continuation

/-!
# HCN.Assembly.LowerBound: the analytic threshold `h ≤ 2 ⇒ dOf m ≤ 4777`

Pinned environment: Lean v4.34.1, Mathlib d13f23b (the openai/math 7/8 environment).

**The interfaces are hypotheses.** The general Chowla–Selberg formula and the class partition were proved separately.
This file uses their statements EXACTLY as written in `HCN.Statements.GeneralCS` and `HCN.Statements.ClassPartition`,
packed as two propositions:
* `CSFacts`: `CS_main_general`, `differentiableOn_mainTermg_add_Eg`, `mainTermg_seven_eighths`,
  `norm_Eg_seven_eighths_le`, `Bg_mono` (each field is the statement verbatim, with its binders made explicit);
* `EFacts hα`: `IsHermite.absNorm_eq`, `IsHermite.C_dvd_A`, `exists_classReps`, for the given field.

Only the DEFINITIONS of the two statement files are used; no `sorry`ed theorem of theirs is referenced, so nothing
here depends on `sorryAx`. `HCN.Main` discharges the two propositions from their proofs.

**The argument** (with the choice of bound explained in `HCN.Numerics.Threshold`):
1. `ζ(s) L(s, χ) = ζ_K(s) = Σ_Cl ½ Z_{Q_Cl}(s) = Σ_Cl (mainTermg + Eg)` on `re s > 1` (CN-1's factorisation,
   `exists_classReps`, `CS_main_general`); both sides are holomorphic on `{re s > 1/2} \ {1}`, so they agree at
   `7/8` (CN-1's `eq_at_ofReal_of_differentiableOn_sdiff`).
2. The left side has real part `ζ(7/8) · L(7/8) ≤ 0`: `ζ(7/8) < 0` (CN-1's numerics) and `L(7/8, χ) ≥ 0` (CN-1's
   positivity, from openai/math's zero-free region `re s > 7/8`).
3. Each class has `a ∈ [1, (2/3)√d]` (Hermite basis and Minkowski), so its real part is at least `Tv d`, and the
   principal class (`a = 1`) at least `Pv d`. With `h ≤ 2` the sum is at least `Pv d + min (Tv d) 0`, which is positive
   for `d ≥ 4778` (`Pv_pos_and_add_Tv_pos`). Contradiction.

The analytic side is stated as `4778 ≤ dOf m → 3 ≤ classNumber K`, the complement of the finite side's
`dOf m < 4778` (one `lt_or_ge` over CN-1's `dOf m`).
-/

set_option autoImplicit false

open NumberField Ideal Complex Set CN1.Finite HCN.CS HCN.Epstein HCN.Numerics
open scoped nonZeroDivisors Real

namespace HCN.Assembly

/-- **The general Chowla–Selberg interface** (`HCN.Statements.GeneralCS`, the statements used here, verbatim). -/
structure CSFacts : Prop where
  CS_main_general : ∀ {a b c : ℝ} {s : ℂ}, 0 < a → 0 < HCN.CS.disc a b c → 1 < s.re →
    (1 / 2 : ℂ) * Zg a b c s = mainTermg a b c s + Eg a b c s
  differentiableOn_mainTermg_add_Eg : ∀ {a b c : ℝ}, 0 < a → 0 < HCN.CS.disc a b c →
    DifferentiableOn ℂ (fun s => mainTermg a b c s + Eg a b c s) ({s : ℂ | 1 / 2 < s.re} \ {1})
  mainTermg_seven_eighths : ∀ {a b c : ℝ}, 0 < a → 0 < HCN.CS.disc a b c →
    mainTermg a b c (7 / 8) =
      ((a ^ (-(7 / 8 : ℝ)) : ℝ) : ℂ) * riemannZeta (7 / 4) +
        ((π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * (Real.sqrt a)⁻¹ *
          (4 * a / (π * HCN.CS.disc a b c)) ^ (3 / 8 : ℝ) : ℝ) : ℂ) * riemannZeta (3 / 4)
  norm_Eg_seven_eighths_le : ∀ {a b c : ℝ}, 0 < a → 0 < HCN.CS.disc a b c →
    ‖Eg a b c (7 / 8)‖ ≤ Bg a (HCN.CS.disc a b c)
  Bg_mono : ∀ {a a' D : ℝ}, 0 < D → 0 < a → a ≤ a' → a' ≤ 2 / 3 * Real.sqrt D → Bg a D ≤ Bg a' D

/-- **The class-partition interface** for one field (`HCN.Statements.ClassPartition`, the statements used here, verbatim). -/
structure EFacts {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) : Prop where
  absNorm_eq : ∀ {J : Ideal (𝓞 K)} {A B C : ℤ}, IsHermite hα J A B C → (absNorm J : ℤ) = A * C
  C_dvd_A : ∀ {J : Ideal (𝓞 K)} {A B C : ℤ}, IsHermite hα J A B C → C ∣ A
  exists_classReps : m ≠ 1 → m ≠ 3 →
    ∃ (J : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰) (A B C : ClassGroup (𝓞 K) → ℤ),
      (∀ Cl, ClassGroup.mk0 (J Cl) = Cl⁻¹) ∧
      (∀ Cl, IsHermite hα (J Cl : Ideal (𝓞 K)) (A Cl) (B Cl) (C Cl)) ∧
      ((J 1 : Ideal (𝓞 K)) = ⊤ ∧ A 1 = 1 ∧ B 1 = 0 ∧ C 1 = 1) ∧
      (∀ Cl, ((absNorm (J Cl : Ideal (𝓞 K)) : ℕ) : ℝ) ≤ 2 / 3 * Real.sqrt (dOf m)) ∧
      ∀ s : ℂ, 1 < s.re → dedekindZeta K s = ∑ Cl : ClassGroup (𝓞 K),
        (1 / 2 : ℂ) * HCN.CS.Zg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) s

section Hermite

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} {hα : α ^ 2 = -(m : K)}

/-- `1 ≤ a` (the proof of `IsHermite.one_le_formA`, from `C_dvd_A`). -/
theorem EFacts.one_le_formA (hE : EFacts hα) {J : Ideal (𝓞 K)} {A B C : ℤ} (h : IsHermite hα J A B C) :
    1 ≤ formA A C := by
  obtain ⟨k, hk⟩ := hE.C_dvd_A h
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

/-- `a ≤ N(J)` (the proof of `IsHermite.formA_le_absNorm`, from `absNorm_eq`). -/
theorem EFacts.formA_le_absNorm (hE : EFacts hα) {J : Ideal (𝓞 K)} {A B C : ℤ} (h : IsHermite hα J A B C) :
    formA A C ≤ absNorm J := by
  have hN := hE.absNorm_eq h
  have hA : (0 : ℝ) < A := by exact_mod_cast h.A_pos
  have hC : (1 : ℝ) ≤ C := by exact_mod_cast h.C_pos
  have hN' : ((absNorm J : ℕ) : ℝ) = A * C := by exact_mod_cast hN
  rw [formA, hN', div_le_iff₀ (by linarith)]
  nlinarith

end Hermite

/-! ### One class at `s = 7/8` -/

/-- For `a ≥ 1`, `coeffg a D = coeffg 1 D · a^{-1/8} ≤ coeffg 1 D`. -/
theorem coeffg_le_coeffg_one {a D : ℝ} (hD : 0 < D) (ha : 1 ≤ a) : coeffg a D ≤ coeffg 1 D := by
  have ha0 : 0 < a := by linarith
  unfold coeffg
  have h4 : (4 * a / (π * D)) ^ (3 / 8 : ℝ) = a ^ (3 / 8 : ℝ) * (4 * 1 / (π * D)) ^ (3 / 8 : ℝ) := by
    rw [← Real.mul_rpow ha0.le (by positivity)]
    congr 1
    ring
  have hsa : a ^ (3 / 8 : ℝ) ≤ Real.sqrt a := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
  have hsa0 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hk : (Real.sqrt a)⁻¹ * a ^ (3 / 8 : ℝ) ≤ 1 := by
    rw [inv_mul_le_iff₀ hsa0, mul_one]
    exact hsa
  have hP : 0 ≤ π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) :=
    div_nonneg (mul_nonneg (by positivity) (Real.Gamma_pos_of_pos (by norm_num)).le)
      (Real.Gamma_pos_of_pos (by norm_num)).le
  have hX : 0 ≤ (4 * 1 / (π * D)) ^ (3 / 8 : ℝ) := by positivity
  rw [h4, Real.sqrt_one, inv_one]
  calc π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * (Real.sqrt a)⁻¹ *
        (a ^ (3 / 8 : ℝ) * (4 * 1 / (π * D)) ^ (3 / 8 : ℝ))
      = π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * ((Real.sqrt a)⁻¹ * a ^ (3 / 8 : ℝ)) *
          (4 * 1 / (π * D)) ^ (3 / 8 : ℝ) := by ring
    _ ≤ π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * 1 * (4 * 1 / (π * D)) ^ (3 / 8 : ℝ) := by
        gcongr
    _ = π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * 1 * (4 * 1 / (π * D)) ^ (3 / 8 : ℝ) := rfl

/-- **One class at `7/8`.** For a positive form with `disc = D`, `1 ≤ a ≤ (2/3)√D`:
`re (mainTermg + Eg)(7/8) ≥ a^{-7/8} ζ(7/4) + coeffg 1 D · ζ(3/4) - Bg((2/3)√D, D)`. -/
theorem re_term_ge (hC : CSFacts) {a b c D : ℝ} (hD : 0 < D) (hdisc : HCN.CS.disc a b c = D) (ha : 1 ≤ a)
    (hamax : a ≤ 2 / 3 * Real.sqrt D) :
    a ^ (-(7 / 8 : ℝ)) * (riemannZeta (7 / 4 : ℂ)).re + coeffg 1 D * (riemannZeta (3 / 4 : ℂ)).re
        - Bg (2 / 3 * Real.sqrt D) D ≤ (mainTermg a b c (7 / 8) + Eg a b c (7 / 8)).re := by
  have ha0 : 0 < a := by linarith
  have hD' : 0 < HCN.CS.disc a b c := hdisc ▸ hD
  have hEn := hC.norm_Eg_seven_eighths_le ha0 hD'
  rw [hdisc] at hEn
  have hmono := hC.Bg_mono hD ha0 hamax le_rfl
  have hEre := (abs_le.mp ((Complex.abs_re_le_norm (Eg a b c (7 / 8))).trans (hEn.trans hmono))).1
  have hco := coeffg_le_coeffg_one hD ha
  have hz34 : (riemannZeta (3 / 4 : ℂ)).re ≤ 0 := CN1.Numerics.riemannZeta_three_quarters_re_neg.le
  have h1 := mul_le_mul_of_nonpos_right hco hz34
  rw [Complex.add_re, hC.mainTermg_seven_eighths ha0 hD', Complex.add_re, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul, hdisc]
  have hcd : π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * (Real.sqrt a)⁻¹ *
      (4 * a / (π * D)) ^ (3 / 8 : ℝ) = coeffg a D := rfl
  rw [hcd]
  linarith

/-! ### The analytic threshold -/

/-- **The analytic side.** For `K = ℚ(√-m)` (`m` squarefree, `m ∉ {1, 3}`), with the two interfaces'
statements as hypotheses: `4778 ≤ dOf m` implies `3 ≤ classNumber K`. -/
theorem three_le_classNumber_of_ge (hC : CSFacts) {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K}
    (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (hE : EFacts hα) (hge : 4778 ≤ dOf m) : 3 ≤ classNumber K := by
  classical
  by_contra h3
  have h2 : Fintype.card (ClassGroup (𝓞 K)) ≤ 2 := by
    have : classNumber K ≤ 2 := by omega
    exact this
  obtain ⟨J, A, B, C, -, hH, ⟨-, hA1, -, hC1⟩, hN, hZ⟩ := hE.exists_classReps hm1 hm3
  have hD : (4778 : ℝ) ≤ (dOf m : ℝ) := by exact_mod_cast hge
  have hD0 : (0 : ℝ) < (dOf m : ℝ) := by linarith
  -- each class: `disc = d`, `1 ≤ a ≤ (2/3)√d`
  have hdisc : ∀ Cl, HCN.CS.disc (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl))
      = (dOf m : ℝ) := fun Cl => disc_form m (hH Cl).A_pos.ne' (hH Cl).C_pos.ne'
  have ha1 : ∀ Cl, 1 ≤ formA (A Cl) (C Cl) := fun Cl => hE.one_le_formA (hH Cl)
  have hamax : ∀ Cl, formA (A Cl) (C Cl) ≤ 2 / 3 * Real.sqrt (dOf m : ℝ) :=
    fun Cl => (hE.formA_le_absNorm (hH Cl)).trans (hN Cl)
  have hpos : ∀ Cl, 0 < formA (A Cl) (C Cl) := fun Cl => by linarith [ha1 Cl]
  have hdpos : ∀ Cl, 0 < HCN.CS.disc (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl))
      (formC m (A Cl) (B Cl) (C Cl)) := fun Cl => by rw [hdisc]; exact hD0
  -- step 1: `ζ L = Σ_Cl (mainTermg + Eg)` on `re s > 1`, continued to `7/8`
  have : NeZero (CN1.Foundations.disc m) := ⟨CN1.Epstein.disc_ne_zero hm.ne_zero⟩
  have hχ1 := CN1.Foundations.kroneckerChar_ne_one hm
  have hLd : Differentiable ℂ (DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m)) :=
    DirichletCharacter.differentiable_LFunction hχ1
  have hF : DifferentiableOn ℂ
      (fun s => riemannZeta s * DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) s)
      ({s : ℂ | 1 / 2 < s.re} \ {1}) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => hs.2 (mem_singleton_iff.mpr h)
    exact ((differentiableAt_riemannZeta hs1).mul (hLd s)).differentiableWithinAt
  have hG : DifferentiableOn ℂ
      (fun s => ∑ Cl : ClassGroup (𝓞 K),
        (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) s +
          Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) s))
      ({s : ℂ | 1 / 2 < s.re} \ {1}) :=
    DifferentiableOn.fun_sum fun Cl _ => hC.differentiableOn_mainTermg_add_Eg (hpos Cl) (hdpos Cl)
  have hFG : ∀ s : ℂ, 1 < s.re →
      riemannZeta s * DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) s =
        ∑ Cl : ClassGroup (𝓞 K),
          (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) s +
            Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) s) := by
    intro s hs
    rw [← CN1.Epstein.dedekindZeta_eq_riemannZeta_mul_LFunction hα hK hm hs, hZ s hs]
    exact Finset.sum_congr rfl fun Cl _ => hC.CS_main_general (hpos Cl) (hdpos Cl) hs
  have h78 := CN1.CS.eq_at_ofReal_of_differentiableOn_sdiff (a := 1 / 2) (x := 7 / 8) (by norm_num)
    (by norm_num) hF hG hFG
  have hc78 : ((7 / 8 : ℝ) : ℂ) = (7 / 8 : ℂ) := by push_cast; ring
  rw [hc78] at h78
  -- step 2: the left side has real part `≤ 0`
  have hre := congrArg Complex.re h78
  rw [Complex.mul_re, CN1.Numerics.riemannZeta_seven_eighths_im, Complex.re_sum] at hre
  obtain ⟨-, hLre⟩ := CN1.LFunction_seven_eighths_nonneg_of_isQuadratic (CN1.Foundations.kroneckerChar m)
    (CN1.Foundations.kroneckerChar_isQuadratic m) hχ1
  have hz78 := CN1.Numerics.riemannZeta_seven_eighths_re_neg
  have hleft : (riemannZeta (7 / 8 : ℂ)).re *
      (DirichletCharacter.LFunction (CN1.Foundations.kroneckerChar m) (7 / 8)).re ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hz78.le hLre
  -- step 3: the class sum is at least `Pv d + min (Tv d) 0 > 0`
  have hP : Pv (dOf m : ℝ) ≤
      (mainTermg (formA (A 1) (C 1)) (formB m (B 1) (C 1)) (formC m (A 1) (B 1) (C 1)) (7 / 8) +
        Eg (formA (A 1) (C 1)) (formB m (B 1) (C 1)) (formC m (A 1) (B 1) (C 1)) (7 / 8)).re := by
    have h := re_term_ge hC hD0 (hdisc 1) (ha1 1) (hamax 1)
    have ha : formA (A 1) (C 1) ^ (-(7 / 8 : ℝ)) = 1 := by simp [hA1, hC1, formA]
    rw [ha, one_mul] at h
    exact h
  have hT : ∀ Cl, Tv (dOf m : ℝ) ≤
      (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) (7 / 8) +
        Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) (7 / 8)).re := by
    intro Cl
    have h := re_term_ge hC hD0 (hdisc Cl) (ha1 Cl) (hamax Cl)
    have hamax0 : 0 < 2 / 3 * Real.sqrt (dOf m : ℝ) := by
      have := Real.sqrt_pos.mpr hD0
      positivity
    have hr : (2 / 3 * Real.sqrt (dOf m : ℝ)) ^ (-(7 / 8 : ℝ)) ≤ formA (A Cl) (C Cl) ^ (-(7 / 8 : ℝ)) :=
      (Real.rpow_le_rpow_iff_of_neg hamax0 (hpos Cl) (by norm_num)).mpr (hamax Cl)
    obtain ⟨z74, hz74, h74lo, -⟩ := CN1.Numerics.riemannZeta_seven_quarters
    have hz : 0 ≤ (riemannZeta (7 / 4 : ℂ)).re := by rw [hz74, Complex.ofReal_re]; linarith
    have := mul_le_mul_of_nonneg_right hr hz
    unfold Tv
    linarith
  have hsum : Pv (dOf m : ℝ) + min (Tv (dOf m : ℝ)) 0 ≤ ∑ Cl : ClassGroup (𝓞 K),
      (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) (7 / 8) +
        Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) (7 / 8)).re := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ClassGroup (𝓞 K)))]
    have hcard : (((Finset.univ : Finset (ClassGroup (𝓞 K))).erase 1).card : ℝ) ≤ 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      have : Fintype.card (ClassGroup (𝓞 K)) - 1 ≤ 1 := by omega
      exact_mod_cast this
    have hs := Finset.card_nsmul_le_sum ((Finset.univ : Finset (ClassGroup (𝓞 K))).erase 1)
      (fun Cl => (mainTermg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) (7 / 8) +
        Eg (formA (A Cl) (C Cl)) (formB m (B Cl) (C Cl)) (formC m (A Cl) (B Cl) (C Cl)) (7 / 8)).re)
      (min (Tv (dOf m : ℝ)) 0) (fun Cl _ => (min_le_left _ _).trans (hT Cl))
    rw [nsmul_eq_mul] at hs
    have hmin : min (Tv (dOf m : ℝ)) 0 ≤ 0 := min_le_right _ _
    have hprod := mul_nonneg_of_nonpos_of_nonpos (by linarith : (((Finset.univ : Finset (ClassGroup (𝓞 K))).erase
      1).card : ℝ) - 1 ≤ 0) hmin
    nlinarith [hP]
  obtain ⟨hPpos, hPT⟩ := Pv_pos_and_add_Tv_pos hD
  have hpos' : 0 < Pv (dOf m : ℝ) + min (Tv (dOf m : ℝ)) 0 := by
    rcases min_cases (Tv (dOf m : ℝ)) 0 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  linarith

/-- **The threshold, in its usual form:** `classNumber K ≤ 2 ⇒ dOf m ≤ 4777` (for `m ∉ {1, 3}`). -/
theorem dOf_le_4777_of_classNumber_le_two (hC : CSFacts) {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K}
    (hα : α ^ 2 = -(m : K)) (hK : Module.finrank ℚ K = 2) (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (hE : EFacts hα) (h2 : classNumber K ≤ 2) : dOf m ≤ 4777 := by
  by_contra hd
  have := three_le_classNumber_of_ge hC hα hK hm hm1 hm3 hE (by omega)
  omega

end HCN.Assembly
