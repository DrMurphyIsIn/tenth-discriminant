import Mathlib

/-!
# The ideal-counting function `a_K(n) = #{I ⊆ 𝓞 K : N(I) = n}` is multiplicative

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib-only; valid for every number field `K`.

`NumberField.dedekindZeta K` is by definition the `L`-series of `n ↦ #{I : absNorm I = n}`
(Mathlib, NumberTheory/NumberField/DedekindZeta.lean). We package that coefficient sequence as the
arithmetic function `idealCount K` (value `0` at `n = 0`) and prove it multiplicative:

* `idealCount_one`: `a_K(1) = 1` (the only ideal of norm `1` is `⊤`);
* `normMulEquiv`: for coprime `a, b ≠ 0`, `{I : N(I) = ab} ≃ {J : N(J) = a} × {J' : N(J') = b}` by
  `I ↦ (I + (a), I + (b))` with inverse `(J, J') ↦ J J'`. The key facts are
  `(I + (a)) (I + (b)) = I` (because `ab = N(I) ∈ I` and `(a) + (b) = (1)`) and
  `N(I + (a)) ∣ gcd(N(I), N((a))) = gcd(ab, a²) = a`, with `N(I + (a)) N(I + (b)) = ab`.

This is the first half of step 2 of the argument (`a_K` multiplicative); the values at prime powers
are in `PrimePower.lean` and `Factorization.lean`.
-/

set_option autoImplicit false

namespace CN1.Epstein

open NumberField Ideal

section CommRing

variable {R : Type*} [CommRing R]

/-- In a commutative ring: if `(x) + (y) = (1)` and `x y ∈ I`, then `(I + (x)) (I + (y)) = I`. -/
theorem sup_span_mul_sup_span_eq {I : Ideal R} {x y : R}
    (hxy : span {x} ⊔ span {y} = ⊤) (hI : x * y ∈ I) :
    (I ⊔ span {x}) * (I ⊔ span {y}) = I := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact Ideal.mul_le_right
    · exact Ideal.mul_le_left
    · exact Ideal.mul_le_right
    · exact (Ideal.span_singleton_le_iff_mem _).mpr hI
  · calc I = I * ⊤ := (Ideal.mul_top I).symm
      _ = I * span {x} ⊔ I * span {y} := by rw [← hxy, Ideal.mul_sup]
      _ ≤ (I ⊔ span {x}) * (I ⊔ span {y}) := by
        refine sup_le ?_ ?_
        · rw [mul_comm]; exact Ideal.mul_mono le_sup_right le_sup_left
        · exact Ideal.mul_mono le_sup_left le_sup_right

/-- In a commutative ring: if `x ∈ J` and `J' + (x) = (1)`, then `J J' + (x) = J`. -/
theorem mul_sup_span_eq {J J' : Ideal R} {x : R} (hx : x ∈ J) (hJ' : J' ⊔ span {x} = ⊤) :
    J * J' ⊔ span {x} = J := by
  apply le_antisymm
  · exact sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  · calc J = J * ⊤ := (Ideal.mul_top J).symm
      _ = J * J' ⊔ J * span {x} := by rw [← hJ', Ideal.mul_sup]
      _ ≤ J * J' ⊔ span {x} := sup_le_sup_left Ideal.mul_le_right _

end CommRing

variable {K : Type*} [Field K] [NumberField K]

/-- For coprime naturals `a, b`, the ideals `(a)` and `(b)` of `𝓞 K` are comaximal. -/
theorem span_natCast_sup_span_natCast_eq_top {a b : ℕ} (hab : a.Coprime b) :
    (span {(a : 𝓞 K)} ⊔ span {(b : 𝓞 K)} : Ideal (𝓞 K)) = ⊤ := by
  rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
  have h := (Nat.isCoprime_iff_coprime.mpr hab).map (Int.castRingHom (𝓞 K))
  simpa using h

/-- A natural-number identity: if `x ∣ a`, `y ∣ b` and `x y = a b` with `a, b ≠ 0`, then `x = a`
and `y = b`. -/
theorem Nat.eq_of_dvd_of_dvd_of_mul_eq_mul {x y a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : x ∣ a) (hy : y ∣ b) (h : x * y = a * b) : x = a ∧ y = b := by
  have hxa := Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hx
  have hyb := Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hy
  have hxeq : x = a := by
    rcases lt_or_eq_of_le hxa with hlt | heq
    · exfalso
      have : x * y < a * b := Nat.mul_lt_mul_of_lt_of_le hlt hyb (Nat.pos_of_ne_zero hb)
      omega
    · exact heq
  subst hxeq
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha) h⟩

/-- For coprime `a, b ≠ 0` and `N(I) = a b`: `N(I + (a)) = a` and `N(I + (b)) = b`. -/
theorem absNorm_sup_span_natCast_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b)
    {I : Ideal (𝓞 K)} (hI : absNorm I = a * b) :
    absNorm (I ⊔ span {(a : 𝓞 K)}) = a ∧ absNorm (I ⊔ span {(b : 𝓞 K)}) = b := by
  have hsup := span_natCast_sup_span_natCast_eq_top (K := K) hab
  have hmem : (a : 𝓞 K) * (b : 𝓞 K) ∈ I := by
    have := absNorm_mem I
    rw [hI] at this
    exact_mod_cast this
  have hprod := sup_span_mul_sup_span_eq hsup hmem
  -- divisibilities
  have hdvdI : absNorm (I ⊔ span {(a : 𝓞 K)}) ∣ a * b :=
    hI ▸ absNorm_dvd_absNorm_of_le le_sup_left
  have hdvdI' : absNorm (I ⊔ span {(b : 𝓞 K)}) ∣ a * b :=
    hI ▸ absNorm_dvd_absNorm_of_le le_sup_left
  have hdvda : absNorm (I ⊔ span {(a : 𝓞 K)}) ∣ a ^ Module.finrank ℤ (𝓞 K) :=
    absNorm_span_natCast (S := 𝓞 K) a ▸ absNorm_dvd_absNorm_of_le le_sup_right
  have hdvdb : absNorm (I ⊔ span {(b : 𝓞 K)}) ∣ b ^ Module.finrank ℤ (𝓞 K) :=
    absNorm_span_natCast (S := 𝓞 K) b ▸ absNorm_dvd_absNorm_of_le le_sup_right
  have hxa : absNorm (I ⊔ span {(a : 𝓞 K)}) ∣ a :=
    (Nat.Coprime.coprime_dvd_left hdvda (Nat.Coprime.pow_left _ hab)).dvd_of_dvd_mul_right hdvdI
  have hyb : absNorm (I ⊔ span {(b : 𝓞 K)}) ∣ b :=
    (Nat.Coprime.coprime_dvd_left hdvdb (Nat.Coprime.pow_left _ hab.symm)).dvd_of_dvd_mul_left
      hdvdI'
  have hmul : absNorm (I ⊔ span {(a : 𝓞 K)}) * absNorm (I ⊔ span {(b : 𝓞 K)}) = a * b := by
    rw [← map_mul, hprod, hI]
  exact Nat.eq_of_dvd_of_dvd_of_mul_eq_mul ha hb hxa hyb hmul

/-- `N(J) = n` gives `(n : 𝓞 K) ∈ J`. -/
theorem natCast_mem_of_absNorm_eq {n : ℕ} {J : Ideal (𝓞 K)} (hJ : absNorm J = n) : (n : 𝓞 K) ∈ J := by
  have := absNorm_mem J
  rwa [hJ] at this

/-- `N(I) = a b` gives `(a : 𝓞 K) * b ∈ I`. -/
theorem natCast_mul_natCast_mem_of_absNorm_eq {a b : ℕ} {I : Ideal (𝓞 K)}
    (hI : absNorm I = a * b) : (a : 𝓞 K) * (b : 𝓞 K) ∈ I := by
  have := natCast_mem_of_absNorm_eq hI
  push_cast at this
  exact this

/-- For coprime `a, b` and `(b : 𝓞 K) ∈ J'`: `J' + (a) = (1)`. -/
theorem sup_span_natCast_eq_top_of_mem {a b : ℕ} (hab : a.Coprime b) {J' : Ideal (𝓞 K)}
    (hbJ' : (b : 𝓞 K) ∈ J') : J' ⊔ span {(a : 𝓞 K)} = ⊤ := by
  rw [eq_top_iff, ← span_natCast_sup_span_natCast_eq_top (K := K) hab]
  exact sup_le le_sup_right (le_sup_of_le_left ((Ideal.span_singleton_le_iff_mem _).mpr hbJ'))

/-- `(I + (a)) (I + (b)) = I` when `N(I) = a b` with `a, b` coprime. -/
theorem sup_span_mul_sup_span_eq_self {a b : ℕ} (hab : a.Coprime b) {I : Ideal (𝓞 K)}
    (hI : absNorm I = a * b) :
    (I ⊔ span {(a : 𝓞 K)}) * (I ⊔ span {(b : 𝓞 K)}) = I :=
  sup_span_mul_sup_span_eq (span_natCast_sup_span_natCast_eq_top hab)
    (natCast_mul_natCast_mem_of_absNorm_eq hI)

/-- `J J' + (a) = J` when `N(J) = a`, `N(J') = b` with `a, b` coprime. -/
theorem mul_sup_span_natCast_eq_left {a b : ℕ} (hab : a.Coprime b) {J J' : Ideal (𝓞 K)}
    (hJ : absNorm J = a) (hJ' : absNorm J' = b) : J * J' ⊔ span {(a : 𝓞 K)} = J :=
  mul_sup_span_eq (natCast_mem_of_absNorm_eq hJ)
    (sup_span_natCast_eq_top_of_mem hab (natCast_mem_of_absNorm_eq hJ'))

/-- `J J' + (b) = J'` when `N(J) = a`, `N(J') = b` with `a, b` coprime. -/
theorem mul_sup_span_natCast_eq_right {a b : ℕ} (hab : a.Coprime b) {J J' : Ideal (𝓞 K)}
    (hJ : absNorm J = a) (hJ' : absNorm J' = b) : J * J' ⊔ span {(b : 𝓞 K)} = J' := by
  rw [mul_comm]
  exact mul_sup_span_eq (natCast_mem_of_absNorm_eq hJ')
    (sup_span_natCast_eq_top_of_mem hab.symm (natCast_mem_of_absNorm_eq hJ))

theorem absNorm_mul_eq {a b : ℕ} {J J' : Ideal (𝓞 K)} (hJ : absNorm J = a) (hJ' : absNorm J' = b) :
    absNorm (J * J') = a * b := by
  rw [map_mul, hJ, hJ']

/-- **Coprime multiplicativity of ideal counts.** For coprime `a, b ≠ 0`,
`{I : N(I) = a b} ≃ {J : N(J) = a} × {J' : N(J') = b}`, by `I ↦ (I + (a), I + (b))`, with inverse
`(J, J') ↦ J J'`. -/
noncomputable def normMulEquiv {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    {I : Ideal (𝓞 K) // absNorm I = a * b} ≃
      {I : Ideal (𝓞 K) // absNorm I = a} × {I : Ideal (𝓞 K) // absNorm I = b} :=
  { toFun := fun I => (⟨I.1 ⊔ span {(a : 𝓞 K)}, (absNorm_sup_span_natCast_eq ha hb hab I.2).1⟩,
      ⟨I.1 ⊔ span {(b : 𝓞 K)}, (absNorm_sup_span_natCast_eq ha hb hab I.2).2⟩)
    invFun := fun J => ⟨J.1.1 * J.2.1, absNorm_mul_eq J.1.2 J.2.2⟩
    left_inv := fun I => Subtype.ext (sup_span_mul_sup_span_eq_self hab I.2)
    right_inv := fun J => Prod.ext (Subtype.ext (mul_sup_span_natCast_eq_left hab J.1.2 J.2.2))
      (Subtype.ext (mul_sup_span_natCast_eq_right hab J.1.2 J.2.2)) }

/-- `#{I : N(I) = a b} = #{I : N(I) = a} · #{I : N(I) = b}` for coprime `a, b ≠ 0`. -/
theorem card_absNorm_eq_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = a * b} =
      Nat.card {I : Ideal (𝓞 K) // absNorm I = a} * Nat.card {I : Ideal (𝓞 K) // absNorm I = b} := by
  rw [Nat.card_congr (normMulEquiv (K := K) ha hb hab), Nat.card_prod]

/-- The only ideal of norm `1` is `⊤`. -/
theorem card_absNorm_eq_one : Nat.card {I : Ideal (𝓞 K) // absNorm I = 1} = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun I J => Subtype.ext ?_⟩, ⟨⟨⊤, absNorm_top⟩⟩⟩
  rw [absNorm_eq_one_iff.mp I.2, absNorm_eq_one_iff.mp J.2]

variable (K)

/-- `a_K(n) = #{I ⊆ 𝓞 K : N(I) = n}` as a complex arithmetic function (value `0` at `n = 0`). -/
noncomputable def idealCount : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun n => (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ))

lemma idealCount_apply {n : ℕ} (hn : n ≠ 0) :
    idealCount K n = (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ) := by
  simp [idealCount, toArithmeticFunction, hn]

/-- The Dedekind zeta function is the `L`-series of `a_K` (Mathlib's definition, up to the
irrelevant value at `n = 0`). -/
theorem dedekindZeta_eq_LSeries_idealCount (s : ℂ) :
    dedekindZeta K s = LSeries (idealCount K) s := by
  unfold dedekindZeta
  exact LSeries_congr (fun hn => (idealCount_apply K hn).symm) s

/-- **`a_K` is multiplicative.** -/
theorem isMultiplicative_idealCount : (idealCount K).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, fun {a b} ha hb hab => ?_⟩
  · rw [idealCount_apply K one_ne_zero, card_absNorm_eq_one]; simp
  · rw [idealCount_apply K (mul_ne_zero ha hb), idealCount_apply K ha, idealCount_apply K hb,
      card_absNorm_eq_mul ha hb hab, Nat.cast_mul]

end CN1.Epstein
