import CN1.ChowlaSelberg.Remainder

/-!
# CN1.ChowlaSelberg.MainTerm: the Chowla–Selberg identity on `re s > 1`

  `½ Z_Q(s) = ζ(2s) + π^s Γ(s - 1/2)/Γ(s) · (4/(πd))^{s - 1/2} ζ(2s - 1) + E_d(s)`,

and `π^s (4/(πd))^{s - 1/2} = 2^{2s - 1} √π d^{1/2 - s}`, which gives the classical form.

Proof. Sum the Poisson slice lemma (`PoissonSlice.lean`) over `y`: the `y = 0` slice is
`Σ_x (x²)^{-s} = 2 ζ(2s)`,
the `k = 0` terms of the slices `y ≠ 0` are `Γ(s - 1/2) (1/a_y)^{s - 1/2}` and sum to
`Γ(s - 1/2) (4/(πd))^{s - 1/2} · 2 ζ(2s - 1)`, and the terms with `y ≠ 0`, `k ≠ 0` form `S_d(s)` (`Remainder.lean`).
-/

open Complex Set MeasureTheory Filter Topology
open scoped Real

namespace CN1.CS

variable {d : ℕ} {s : ℂ}

/-- The main term `ζ(2s) + π^s Γ(s - 1/2) Γ(s)⁻¹ (4/(πd))^{s - 1/2} ζ(2s - 1)`. -/
noncomputable def mainTerm (d : ℕ) (s : ℂ) : ℂ :=
  riemannZeta (2 * s) + (π : ℂ) ^ s * Gamma (s - 1 / 2) * (Gamma s)⁻¹ *
    ((4 / (π * d) : ℝ) : ℂ) ^ (s - 1 / 2) * riemannZeta (2 * s - 1)

/-! ### `Σ_{x ∈ ℤ} (x²)^{-w} = 2 ζ(2w)` for `re w > 1/2` -/

lemma sq_cpow_eq_one_div (n : ℕ) {w : ℂ} (hw : w ≠ 0) :
    (((n : ℝ) ^ 2 : ℝ) : ℂ) ^ (-w) = 1 / (n : ℂ) ^ (2 * w) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h2w : 2 * w ≠ 0 := mul_ne_zero two_ne_zero hw
    simp [Complex.zero_cpow (neg_ne_zero.mpr hw), Complex.zero_cpow h2w]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
      cpow_pos_eq_exp (by positivity), cpow_pos_eq_exp hn', one_div, ← Complex.exp_neg,
      Real.log_pow]
    congr 1
    push_cast
    ring

theorem tsum_int_sq_cpow {w : ℂ} (hw : 1 / 2 < w.re) :
    ∑' x : ℤ, (((x : ℝ) ^ 2 : ℝ) : ℂ) ^ (-w) = 2 * riemannZeta (2 * w) := by
  have h2w : 1 < (2 * w).re := by simp; linarith
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw; linarith
  have hterm : ∀ n : ℕ, (((n : ℝ) ^ 2 : ℝ) : ℂ) ^ (-w) = 1 / (n : ℂ) ^ (2 * w) :=
    fun n => sq_cpow_eq_one_div n hw0
  have hf : Summable fun n : ℕ => (((n : ℝ) ^ 2 : ℝ) : ℂ) ^ (-w) := by
    simp_rw [hterm]; exact Complex.summable_one_div_nat_cpow.mpr h2w
  set f : ℤ → ℂ := fun x => (((x : ℝ) ^ 2 : ℝ) : ℂ) ^ (-w) with hfdef
  have heven : Function.Even f := fun x => by simp [f]
  have hnat : ∀ n : ℕ, f (n : ℤ) = (((n : ℝ) ^ 2 : ℝ) : ℂ) ^ (-w) := fun n => by simp [f]
  have hneg : ∀ n : ℕ, f (-(n : ℤ)) = (((n : ℝ) ^ 2 : ℝ) : ℂ) ^ (-w) := fun n => by simp [f]
  have hsum : Summable f := by
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨hf.congr fun n => (hnat n).symm, hf.congr fun n => (hneg n).symm⟩
  have hf0 : f 0 = 0 := by simp [f, Complex.zero_cpow (neg_ne_zero.mpr hw0)]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum, hf0, zero_add, nsmul_eq_mul,
    Nat.cast_ofNat]
  congr 1
  rw [tsum_pnat_eq_tsum_of_eq_zero (f := fun n : ℕ => f (n : ℤ)) hf0,
    zeta_eq_tsum_one_div_nat_cpow h2w]
  exact tsum_congr fun n => by rw [hnat, hterm]

/-! ### The `y = 0` slice -/

lemma Q_zero_right (d : ℕ) (x : ℤ) : Q d x 0 = (x : ℝ) ^ 2 := by simp [Q]

theorem tsum_slice_zero (hs : 1 / 2 < s.re) :
    ∑' x : ℤ, (Q d x 0 : ℂ) ^ (-s) = 2 * riemannZeta (2 * s) := by
  simp_rw [Q_zero_right]
  exact tsum_int_sq_cpow hs

/-! ### The `k = 0` terms of the slices `y ≠ 0` -/

lemma one_div_ay (hd : 1 ≤ d) {y : ℤ} (hy : y ≠ 0) :
    (1 / (ay d y : ℂ)) = ((4 / (π * d) * ((y : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
  unfold ay
  push_cast
  field_simp

/-- The `k = 0` term for `y ≠ 0`, and `0` for `y = 0`, in closed form. -/
lemma I_zero_term (hd3 : 3 ≤ d) {s : ℂ} (hs : 1 / 2 < s.re) (y : ℤ) :
    (if y = 0 then 0 else I s (ay d y) 0) =
      Gamma (s - 1 / 2) * ((4 / (π * d) : ℝ) : ℂ) ^ (s - 1 / 2) *
        (((y : ℝ) ^ 2 : ℝ) : ℂ) ^ (-(s - 1 / 2)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 1 ≤ d)
  have hs0 : s - 1 / 2 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  split_ifs with hy
  · subst hy
    have h0 : (((0 : ℤ) : ℝ) ^ 2 : ℝ) = 0 := by simp
    rw [h0, Complex.ofReal_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0), mul_zero]
  · rw [I_zero (ay_pos hd3 hy) hs, one_div_ay (by omega) hy,
      cpow_mul_ofReal (by positivity) (inv_pos.mpr (by positivity)),
      cpow_inv_ofReal (by positivity)]
    ring

theorem tsum_I_zero (hd3 : 3 ≤ d) {s : ℂ} (hs : 1 < s.re) :
    ∑' y : ℤ, (if y = 0 then 0 else I s (ay d y) 0) =
      Gamma (s - 1 / 2) * ((4 / (π * d) : ℝ) : ℂ) ^ (s - 1 / 2) * (2 * riemannZeta (2 * s - 1)) := by
  have hs' : 1 / 2 < s.re := by linarith
  simp_rw [I_zero_term hd3 hs']
  rw [tsum_mul_left, tsum_int_sq_cpow (by simp; linarith)]
  congr 3
  ring

lemma summable_I_zero (hd3 : 3 ≤ d) {s : ℂ} (hs : 1 < s.re) :
    Summable fun y : ℤ => (if y = 0 then 0 else I s (ay d y) 0) := by
  have hs' : 1 / 2 < s.re := by linarith
  simp_rw [I_zero_term hd3 hs']
  refine Summable.mul_left _ ?_
  -- summability of `y ↦ (y²)^{-(s - 1/2)}` over `ℤ`, from the `ℕ`-summability of `1/n^{2s-1}`
  have hw0 : s - 1 / 2 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  have h2w : 1 < (2 * (s - 1 / 2)).re := by simp; linarith
  have hf : Summable fun n : ℕ => (((n : ℝ) ^ 2 : ℝ) : ℂ) ^ (-(s - 1 / 2)) := by
    simp_rw [sq_cpow_eq_one_div _ hw0]; exact Complex.summable_one_div_nat_cpow.mpr h2w
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨hf.congr fun n => by simp, hf.congr fun n => by simp⟩

/-! ### Assembly -/

/-- The slice `y ≠ 0` with the `k = 0` term separated. -/
lemma slice_split (hd : IsDisc d) (h3 : 3 ≤ d) (hs : 1 < s.re) {y : ℤ} (hy : y ≠ 0) :
    ∑' x : ℤ, (Q d x y : ℂ) ^ (-s) =
      (π : ℂ) ^ s / Gamma s * (I s (ay d y) 0 + ∑' k : ℤ, Rterm d s (y, k)) := by
  rw [slice hd h3 hs hy]
  congr 1
  have hs' : 1 / 2 < s.re := by linarith
  have hsum : Summable fun k : ℤ => sgn d k y * I s (ay d y) (bk k) := by
    have h1 := (summable_Rterm h3 hs').prod_factor y
    have h2 : Summable fun k : ℤ => if k = 0 then sgn d 0 y * I s (ay d y) (bk 0) else 0 :=
      (hasSum_ite_eq 0 _).summable
    refine (h1.add h2).congr fun k => ?_
    by_cases hk : k = 0
    · subst hk; simp [Rterm, hy]
    · simp [Rterm, hy, hk]
  rw [hsum.tsum_eq_add_tsum_ite 0]
  congr 1
  · simp [sgn, bk]
  · exact tsum_congr fun k => by by_cases hk : k = 0 <;> simp [Rterm, hy, hk]

/-- **Chowla–Selberg with explicit remainder, on `re s > 1`:**
`½ Z_Q(s) = ζ(2s) + π^s Γ(s - 1/2)/Γ(s) (4/(πd))^{s - 1/2} ζ(2s - 1) + E_d(s)`. -/
theorem CS_main (hd : IsDisc d) (h3 : 3 ≤ d) (hs : 1 < s.re) :
    (1 / 2 : ℂ) * Z d s = mainTerm d s + E d s := by
  have hs' : 1 / 2 < s.re := by linarith
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hZ : Z d s = ∑' y : ℤ, ∑' x : ℤ, (Q d x y : ℂ) ^ (-s) := by
    have e := (Equiv.prodComm ℤ ℤ).tsum_eq (fun p : ℤ × ℤ => (Q d p.1 p.2 : ℂ) ^ (-s))
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] at e
    rw [Z, ← e]
    exact (summable_Q_cpow hd h3 hs).prod_symm.tsum_prod' fun y => summable_Q_cpow_slice hd h3 hs y
  have hT : ∀ y : ℤ, ∑' x : ℤ, (Q d x y : ℂ) ^ (-s) =
      (if y = 0 then 2 * riemannZeta (2 * s) else 0) +
        (π : ℂ) ^ s / Gamma s *
          ((if y = 0 then 0 else I s (ay d y) 0) + ∑' k : ℤ, Rterm d s (y, k)) := by
    intro y
    by_cases hy : y = 0
    · subst hy
      simp only [if_true]
      rw [tsum_slice_zero hs']
      have h0 : ∀ k : ℤ, Rterm d s (0, k) = 0 := fun k => by simp [Rterm]
      simp [h0]
    · simp only [if_neg hy]
      rw [slice_split hd h3 hs hy, zero_add]
  have hD : Summable fun y : ℤ => (if y = 0 then 2 * riemannZeta (2 * s) else 0) :=
    (hasSum_ite_eq 0 _).summable
  have hA := summable_I_zero h3 hs
  have hR : Summable fun y : ℤ => ∑' k : ℤ, Rterm d s (y, k) :=
    ((summable_Rterm h3 hs').hasSum.prod_fiberwise fun y =>
      ((summable_Rterm h3 hs').prod_factor y).hasSum).summable
  rw [hZ]
  simp_rw [hT]
  rw [hD.tsum_add ((hA.add hR).mul_left _), tsum_ite_eq 0 (fun _ => 2 * riemannZeta (2 * s)),
    tsum_mul_left, hA.tsum_add hR, tsum_I_zero h3 hs, ← S_eq_tsum_tsum h3 hs']
  unfold mainTerm E
  field_simp
  ring

/-! ### The classical form of the main term, and its value at `s = 7/8` -/

/-- `π^s (4/(πd))^{s - 1/2} = 2^{2s - 1} √π d^{1/2 - s}`. -/
theorem pi_cpow_mul_four_div (hd : 1 ≤ d) (s : ℂ) :
    (π : ℂ) ^ s * ((4 / (π * d) : ℝ) : ℂ) ^ (s - 1 / 2) =
      (2 : ℂ) ^ (2 * s - 1) * (Real.sqrt π : ℂ) * (d : ℂ) ^ (1 / 2 - s) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h4 : (0 : ℝ) < 4 / (π * d) := by positivity
  have h2 : (2 : ℂ) ^ (2 * s - 1) = cexp ((2 * s - 1) * (Real.log 2 : ℂ)) := by
    have := cpow_pos_eq_exp (two_pos : (0 : ℝ) < 2) (2 * s - 1)
    simpa using this
  have hd2 : (d : ℂ) ^ (1 / 2 - s) = cexp ((1 / 2 - s) * (Real.log d : ℂ)) := by
    have := cpow_pos_eq_exp hd' (1 / 2 - s)
    simpa using this
  have hsq : (Real.sqrt π : ℂ) = cexp ((1 / 2 : ℂ) * (Real.log π : ℂ)) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le, cpow_pos_eq_exp Real.pi_pos]
    congr 1
    push_cast
    ring
  have hlog : Real.log (4 / (π * d)) = 2 * Real.log 2 - Real.log π - Real.log d := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_mul Real.pi_pos.ne' hd'.ne',
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h2, hd2, hsq, cpow_pos_eq_exp Real.pi_pos, cpow_pos_eq_exp h4, hlog]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The classical Chowla–Selberg form on `re s > 1`:
`½ Z_Q(s) = ζ(2s) + 2^{2s-1} √π Γ(s - 1/2)/Γ(s) d^{1/2 - s} ζ(2s - 1) + E_d(s)`. -/
theorem CS_main_classical (hd : IsDisc d) (h3 : 3 ≤ d) (hs : 1 < s.re) :
    (1 / 2 : ℂ) * Z d s = riemannZeta (2 * s) +
      (2 : ℂ) ^ (2 * s - 1) * (Real.sqrt π : ℂ) * Gamma (s - 1 / 2) / Gamma s *
        (d : ℂ) ^ (1 / 2 - s) * riemannZeta (2 * s - 1) + E d s := by
  rw [CS_main hd h3 hs, mainTerm]
  congr 2
  have h := pi_cpow_mul_four_div (d := d) (by omega) s
  linear_combination (Gamma (s - 1 / 2) * (Gamma s)⁻¹ * riemannZeta (2 * s - 1)) * h

/-- The main term at `s = 7/8`, with a real coefficient:
`ζ(7/4) + π^{7/8} Γ(3/8)/Γ(7/8) (4/(πd))^{3/8} · ζ(3/4)`. -/
theorem mainTerm_seven_eighths :
    mainTerm d (7 / 8) = riemannZeta (7 / 4) +
      ((π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) *
        (4 / (π * d)) ^ (3 / 8 : ℝ) : ℝ) : ℂ) * riemannZeta (3 / 4) := by
  unfold mainTerm
  have h1 : (2 : ℂ) * (7 / 8) = 7 / 4 := by norm_num
  have h2 : (2 : ℂ) * (7 / 8) - 1 = 3 / 4 := by norm_num
  have h3 : (7 / 8 : ℂ) - 1 / 2 = ((3 / 8 : ℝ) : ℂ) := by push_cast; norm_num
  have h0 : (7 / 8 : ℂ) = ((7 / 8 : ℝ) : ℂ) := by push_cast; ring
  rw [h2, h1, h3, h0, ← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal, ← Complex.ofReal_cpow (by positivity)]
  push_cast
  ring

/-- The main term is holomorphic on `{re s > 1/2} \ {1}`. -/
theorem differentiableOn_mainTerm (hd : 1 ≤ d) :
    DifferentiableOn ℂ (mainTerm d) ({s : ℂ | 1 / 2 < s.re} \ {1}) := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  simp only [mem_setOf_eq] at hs1
  have hs2' : s ≠ 1 := fun h => hs2 (mem_singleton_iff.mpr h)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply DifferentiableAt.differentiableWithinAt
  have hz1 : DifferentiableAt ℂ (fun s => riemannZeta (2 * s)) s := by
    refine (differentiableAt_riemannZeta ?_).comp s (differentiableAt_id.const_mul 2)
    intro h
    have := congrArg re h
    simp at this
    linarith
  have hz2 : DifferentiableAt ℂ (fun s => riemannZeta (2 * s - 1)) s := by
    refine (differentiableAt_riemannZeta ?_).comp s ((differentiableAt_id.const_mul 2).sub_const 1)
    intro h
    exact hs2' (by linear_combination (1 / 2 : ℂ) * h)
  have hπ : DifferentiableAt ℂ (fun s : ℂ => (π : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr Real.pi_pos.ne'))
  have hΓ : DifferentiableAt ℂ (fun s : ℂ => Gamma (s - 1 / 2)) s := by
    refine (differentiableAt_Gamma _ ?_).comp s (differentiableAt_id.sub_const _)
    intro m h
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hΓi : DifferentiableAt ℂ (fun s : ℂ => (Gamma s)⁻¹) s :=
    Complex.differentiable_one_div_Gamma s
  have h4 : DifferentiableAt ℂ (fun s : ℂ => ((4 / (π * d) : ℝ) : ℂ) ^ (s - 1 / 2)) s :=
    (differentiableAt_id.sub_const _).const_cpow
      (Or.inl (ofReal_ne_zero.mpr (by positivity)))
  exact hz1.add ((((hπ.mul hΓ).mul hΓi).mul h4).mul hz2)

end CN1.CS
