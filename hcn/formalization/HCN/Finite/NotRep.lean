import Mathlib

/-!
# HCN.Finite.NotRep: kernel-decidable non-representation by the principal form

The principal form is `Q(x, y) = x² + t·x·y + c·y²`, with
`4·Q(x, y) = (2x + t·y)² + d·y²` and `d = 4c - t²`. So `Q` represents `n` iff there are naturals `y` and `z`
with `z² + d·y² = 4n` and `z ≡ t·y (mod 2)`: put `z = |2x + t·y|`, and use `(x, y) ↦ (-x, -y)` to make `y ≥ 0`.

* `NotRep t c n`: no `y ≥ 0` works, i.e. `Q` does not represent `n`;
* `NotRepYNonzero t c n`: no `y ≥ 1` works, i.e. every solution of `Q(x, y) = n` has `y = 0`.

Both are `Bool` searches over `ℕ`, upward in `y` until `d·y² > 4n`, and for each `y` upward in `z` until
`z² > 4n - d·y²`. Each loop carries fuel `4n + 1` (always enough when `d ≥ 1`); running out of fuel answers
"represented", so fuel can only make the test fail, never pass wrongly. The kernel unfolds only the steps
actually taken, about `√(4n/d) + 1` values of `y` and `2√n + 1` values of `z`.

The soundness lemmas (`NotRep.sound`, `NotRepYNonzero.sound`) need only `t² ≤ 4c`. They generalise CN-1's
`CN1.Finite.not_form_eq_prime`, which is the case `4n ≤ d`. Pure integer arithmetic, no number field.
-/

namespace HCN.Finite

/-- `sqFrom s e f z`: is there `w ≥ z` with `w * w = s` and `w % 2 = e`? Scans `w = z, z + 1, ...` and stops
(answering `false`) once `w * w > s`; out of fuel it answers `true`. -/
def sqFrom (s e : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, z => if s < z * z then false else (z * z == s && z % 2 == e) || sqFrom s e f (z + 1)

theorem sqFrom_eq_false {s e : ℕ} :
    ∀ {f z : ℕ}, sqFrom s e f z = false → ∀ w, z ≤ w → w * w = s → w % 2 ≠ e := by
  intro f
  induction f with
  | zero => intro z h; simp [sqFrom] at h
  | succ f ih =>
    intro z h w hzw hw
    unfold sqFrom at h
    split_ifs at h with hlt
    · have : z * z ≤ w * w := Nat.mul_le_mul hzw hzw
      omega
    · simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
      obtain ⟨h1, h2⟩ := h
      rcases Nat.eq_or_lt_of_le hzw with rfl | hlt'
      · rcases h1 with h1 | h1
        · exact absurd hw h1
        · exact h1
      · exact ih h2 w hlt' hw

/-- `noRepFrom t d n f y`: no `y' ≥ y` and `z` with `z * z + d * (y' * y') = 4 * n` and `z ≡ t * y' (mod 2)`.
Scans `y' = y, y + 1, ...` and stops (answering `true`) once `d * y'² > 4n`; out of fuel it answers `false`. -/
def noRepFrom (t d n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, y =>
    if 4 * n < d * (y * y) then true
    else !(sqFrom (4 * n - d * (y * y)) (t * y % 2) (4 * n + 1) 0) && noRepFrom t d n f (y + 1)

theorem noRepFrom_eq_true {t d n : ℕ} :
    ∀ {f y : ℕ}, noRepFrom t d n f y = true →
      ∀ y', y ≤ y' → ∀ z, z * z + d * (y' * y') = 4 * n → z % 2 ≠ t * y' % 2 := by
  intro f
  induction f with
  | zero => intro y h; simp [noRepFrom] at h
  | succ f ih =>
    intro y h y' hyy z hz
    unfold noRepFrom at h
    split_ifs at h with hlt
    · have : d * (y * y) ≤ d * (y' * y') := Nat.mul_le_mul_left d (Nat.mul_le_mul hyy hyy)
      omega
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨h1, h2⟩ := h
      rcases Nat.eq_or_lt_of_le hyy with rfl | hlt'
      · exact sqFrom_eq_false h1 z (Nat.zero_le z) (by omega)
      · exact ih h2 y' hlt' z hz

/-- **`Q` does not represent `n`**, as a kernel-decidable search (`d = 4c - t²`). -/
def NotRep (t c n : ℕ) : Prop := noRepFrom t (4 * c - t * t) n (4 * n + 1) 0 = true

/-- **Every solution of `Q(x, y) = n` has `y = 0`**, as a kernel-decidable search. -/
def NotRepYNonzero (t c n : ℕ) : Prop := noRepFrom t (4 * c - t * t) n (4 * n + 1) 1 = true

instance (t c n : ℕ) : Decidable (NotRep t c n) := inferInstanceAs (Decidable (_ = true))

instance (t c n : ℕ) : Decidable (NotRepYNonzero t c n) := inferInstanceAs (Decidable (_ = true))

/-- An integer solution of `Q(x, y) = n` with `y ≥ 0` gives the natural pair `(z, y)` of the search. -/
theorem exists_nat_of_form_eq {t c : ℕ} (htc : t * t ≤ 4 * c) {n : ℕ} {x y : ℤ} (hy : 0 ≤ y)
    (h : x ^ 2 + (t : ℤ) * x * y + (c : ℤ) * y ^ 2 = n) :
    ∃ z : ℕ, z * z + (4 * c - t * t) * (y.toNat * y.toNat) = 4 * n ∧ z % 2 = t * y.toNat % 2 := by
  refine ⟨(2 * x + t * y).natAbs, ?_, ?_⟩
  · have hyc : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy
    have hd : (((4 * c - t * t : ℕ)) : ℤ) = 4 * c - t * t := by push_cast [Nat.cast_sub htc]; ring
    have key : (((2 * x + t * y).natAbs * (2 * x + t * y).natAbs +
        (4 * c - t * t) * (y.toNat * y.toNat) : ℕ) : ℤ) = ((4 * n : ℕ) : ℤ) := by
      push_cast
      rw [hd, hyc, ← sq, sq_abs]
      linear_combination 4 * h
    exact_mod_cast key
  · have hyc : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy
    have habs := Int.natAbs_eq (2 * x + t * y)
    have hw : ((t * y.toNat : ℕ) : ℤ) = (t : ℤ) * y := by push_cast; rw [hyc]
    omega

/-- **Soundness of `NotRep`**: `Q(x, y) ≠ n` for all integers `x, y`. -/
theorem NotRep.sound {t c n : ℕ} (htc : t * t ≤ 4 * c) (h : NotRep t c n) (x y : ℤ) :
    x ^ 2 + (t : ℤ) * x * y + (c : ℤ) * y ^ 2 ≠ n := by
  intro hxy
  -- reduce to `y ≥ 0` by `(x, y) ↦ (-x, -y)`
  obtain ⟨x', y', hy', hxy'⟩ : ∃ x' y' : ℤ, 0 ≤ y' ∧ x' ^ 2 + (t : ℤ) * x' * y' + (c : ℤ) * y' ^ 2 = n := by
    rcases le_total 0 y with hy | hy
    · exact ⟨x, y, hy, hxy⟩
    · exact ⟨-x, -y, by linarith, by rw [← hxy]; ring⟩
  obtain ⟨z, hz, hpar⟩ := exists_nat_of_form_eq htc hy' hxy'
  exact noRepFrom_eq_true h y'.toNat (Nat.zero_le _) z hz hpar

/-- **Soundness of `NotRepYNonzero`**: every integer solution of `Q(x, y) = n` has `y = 0`. -/
theorem NotRepYNonzero.sound {t c n : ℕ} (htc : t * t ≤ 4 * c) (h : NotRepYNonzero t c n) (x y : ℤ)
    (hxy : x ^ 2 + (t : ℤ) * x * y + (c : ℤ) * y ^ 2 = n) : y = 0 := by
  by_contra hy0
  obtain ⟨x', y', hy', hy'0, hxy'⟩ :
      ∃ x' y' : ℤ, 0 < y' ∧ y' ≠ 0 ∧ x' ^ 2 + (t : ℤ) * x' * y' + (c : ℤ) * y' ^ 2 = n := by
    rcases lt_or_gt_of_ne hy0 with hy | hy
    · exact ⟨-x, -y, by linarith, by omega, by rw [← hxy]; ring⟩
    · exact ⟨x, y, hy, hy0, hxy⟩
  obtain ⟨z, hz, hpar⟩ := exists_nat_of_form_eq htc hy'.le hxy'
  exact noRepFrom_eq_true h y'.toNat (by omega) z hz hpar

end HCN.Finite
