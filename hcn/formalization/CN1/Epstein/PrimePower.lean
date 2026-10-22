import Mathlib

/-!
# Counting ideals of norm `p ^ k` from the primes over `p`

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Mathlib-only; valid for every number field `K`.

If `N(I) = p ^ k` then every prime factor `P` of `I` contains `N(I) = p ^ k`, hence `p`, so `P` lies
over `(p)` (`mem_primesOver_of_mem_normalizedFactors`). Unique factorisation of ideals then gives the
counts in the two shapes a quadratic field produces:

* one prime `P` over `p` with `N(P) = p ^ f` (inert, `f = 2`; ramified, `f = 1`): the ideals of norm
  `p ^ k` are exactly `P ^ (k / f)` when `f ∣ k`, and there are none otherwise
  (`card_absNorm_eq_pow_of_ncard_eq_one`);
* two primes `P₁ ≠ P₂` over `p`, both of norm `p` (split): the ideals of norm `p ^ k` are
  `P₁ ^ i P₂ ^ (k - i)`, `0 ≤ i ≤ k`, so there are `k + 1` (`card_absNorm_eq_pow_of_ncard_eq_two`).
-/

set_option autoImplicit false

namespace CN1.Epstein

open NumberField Ideal UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]

/-- A prime of `𝓞 K` containing `p` lies over `(p)`. -/
theorem mem_primesOver_of_mem {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hpP : (p : 𝓞 K) ∈ P) :
    P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by
  haveI := hP
  refine ⟨hP, ⟨?_⟩⟩
  have hmax : (span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp.out)).isMaximal (by simpa using hp.out.ne_zero)
  refine hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
  simpa using hpP

/-- An ideal of norm `p ^ k` is nonzero. -/
theorem ne_bot_of_absNorm_eq_pow {I : Ideal (𝓞 K)} {k : ℕ} (hI : absNorm I = p ^ k) : I ≠ ⊥ := by
  intro h
  rw [h, absNorm_bot] at hI
  exact pow_ne_zero _ hp.out.ne_zero hI.symm

/-- Every prime factor of an ideal of norm `p ^ k` lies over `p`. -/
theorem mem_primesOver_of_mem_normalizedFactors {I P : Ideal (𝓞 K)} {k : ℕ}
    (hI : absNorm I = p ^ k) (hP : P ∈ normalizedFactors I) :
    P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by
  have hPp : P.IsPrime := Ideal.isPrime_of_prime (prime_of_normalized_factor P hP)
  have hle : I ≤ P := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)
  apply mem_primesOver_of_mem p hPp
  apply hPp.mem_of_pow_mem k
  have := absNorm_mem I
  rw [hI] at this
  push_cast at this
  exact hle this

/-- A member of `primesOver (p)` has norm `p ^ (inertia degree)`. -/
theorem absNorm_eq_pow_inertiaDeg_of_mem_primesOver {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) : absNorm P = p ^ P.inertiaDeg ℤ := by
  haveI := hP.1
  haveI := hP.2
  exact (Ideal.pow_inertiaDeg p P).symm

/-! ### One prime over `p` -/

/-- If `P` is the only prime over `p` and `N(P) = p ^ f` with `f > 0`, the ideals of norm `p ^ k`
are exactly `P ^ (k / f)` when `f ∣ k`, and there are none otherwise. -/
theorem card_absNorm_eq_pow_of_primesOver_eq_singleton {P : Ideal (𝓞 K)}
    (hS : primesOver (span {(p : ℤ)}) (𝓞 K) = {P}) {f : ℕ} (hf : 0 < f)
    (hN : absNorm P = p ^ f) (k : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = p ^ k} = if f ∣ k then 1 else 0 := by
  have key : ∀ I : Ideal (𝓞 K), absNorm I = p ^ k → ∃ n, I = P ^ n ∧ f * n = k := by
    intro I hI
    have hI0 : I ≠ ⊥ := ne_bot_of_absNorm_eq_pow p hI
    have hall : ∀ Q ∈ normalizedFactors I, Q = P := fun Q hQ => by
      have := mem_primesOver_of_mem_normalizedFactors p hI hQ
      rw [hS] at this
      exact this
    have hrep : normalizedFactors I = Multiset.replicate (Multiset.card (normalizedFactors I)) P :=
      Multiset.eq_replicate_card.mpr hall
    have hprod : I = P ^ Multiset.card (normalizedFactors I) := by
      conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0, hrep, Multiset.prod_replicate]
    refine ⟨_, hprod, ?_⟩
    have := hI
    rw [hprod, map_pow, hN, ← pow_mul] at this
    exact Nat.pow_right_injective hp.out.two_le this
  split_ifs with hfk
  · obtain ⟨n, rfl⟩ := hfk
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun I J => ?_⟩, ⟨⟨P ^ n, by rw [map_pow, hN, ← pow_mul]⟩⟩⟩
    obtain ⟨nI, hI, hnI⟩ := key I.1 I.2
    obtain ⟨nJ, hJ, hnJ⟩ := key J.1 J.2
    have : nI = nJ := Nat.eq_of_mul_eq_mul_left hf (hnI.trans hnJ.symm)
    exact Subtype.ext (by rw [hI, hJ, this])
  · haveI : IsEmpty {I : Ideal (𝓞 K) // absNorm I = p ^ k} :=
      ⟨fun I => by obtain ⟨n, _, hn⟩ := key I.1 I.2; exact hfk ⟨n, hn.symm⟩⟩
    exact Nat.card_of_isEmpty

/-- The same, from `ncard (primesOver (p)) = 1` and a common inertia degree `f`. -/
theorem card_absNorm_eq_pow_of_ncard_eq_one
    (h1 : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1) {f : ℕ} (hf : 0 < f)
    (hdeg : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = f) (k : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = p ^ k} = if f ∣ k then 1 else 0 := by
  obtain ⟨P, hS⟩ := Set.ncard_eq_one.mp h1
  have hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by rw [hS]; exact Set.mem_singleton P
  have hN : absNorm P = p ^ f := by
    rw [absNorm_eq_pow_inertiaDeg_of_mem_primesOver p hP, hdeg P hP]
  exact card_absNorm_eq_pow_of_primesOver_eq_singleton p hS hf hN k

/-! ### Two primes over `p` -/

/-- If `P₁ ≠ P₂` are the primes over `p`, both of norm `p`, there are exactly `k + 1` ideals of
norm `p ^ k`, namely `P₁ ^ i P₂ ^ (k - i)` for `0 ≤ i ≤ k`. -/
theorem card_absNorm_eq_pow_of_primesOver_eq_pair {P₁ P₂ : Ideal (𝓞 K)} (hne : P₁ ≠ P₂)
    (hS : primesOver (span {(p : ℤ)}) (𝓞 K) = {P₁, P₂})
    (hN₁ : absNorm P₁ = p) (hN₂ : absNorm P₂ = p) (k : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = p ^ k} = k + 1 := by
  classical
  have hP₁ : P₁ ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by rw [hS]; simp
  have hP₂ : P₂ ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by rw [hS]; simp
  have hP₁0 : P₁ ≠ ⊥ := ne_bot_of_absNorm_eq_pow p (k := 1) (by rw [hN₁, pow_one])
  have hP₂0 : P₂ ≠ ⊥ := ne_bot_of_absNorm_eq_pow p (k := 1) (by rw [hN₂, pow_one])
  have hirr₁ : Irreducible P₁ := (Ideal.prime_of_isPrime hP₁0 hP₁.1).irreducible
  have hirr₂ : Irreducible P₂ := (Ideal.prime_of_isPrime hP₂0 hP₂.1).irreducible
  have hcount : ∀ i j : ℕ, (normalizedFactors (P₁ ^ i * P₂ ^ j)).count P₁ = i := by
    intro i j
    rw [normalizedFactors_mul (pow_ne_zero _ hP₁0) (pow_ne_zero _ hP₂0), normalizedFactors_pow,
      normalizedFactors_pow, normalizedFactors_irreducible hirr₁,
      normalizedFactors_irreducible hirr₂, normalize_eq, normalize_eq, Multiset.count_add,
      Multiset.count_nsmul, Multiset.count_nsmul, Multiset.count_singleton_self,
      Multiset.count_singleton, if_neg hne]
    simp
  let φ : Fin (k + 1) → {I : Ideal (𝓞 K) // absNorm I = p ^ k} := fun i =>
    ⟨P₁ ^ (i : ℕ) * P₂ ^ (k - i), by
      rw [map_mul, map_pow, map_pow, hN₁, hN₂, ← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp i.2)]⟩
  have hinj : Function.Injective φ := by
    intro i j hij
    have := congrArg (fun I : {I : Ideal (𝓞 K) // absNorm I = p ^ k} =>
      (normalizedFactors I.1).count P₁) hij
    simp only [φ, hcount] at this
    exact Fin.ext this
  have hsurj : Function.Surjective φ := by
    rintro ⟨I, hI⟩
    have hI0 : I ≠ ⊥ := ne_bot_of_absNorm_eq_pow p hI
    have hall : ∀ Q ∈ normalizedFactors I, Q = P₁ ∨ Q = P₂ := fun Q hQ => by
      have := mem_primesOver_of_mem_normalizedFactors p hI hQ
      rw [hS] at this
      simpa using this
    set c₁ := (normalizedFactors I).count P₁ with hc₁
    set c₂ := (normalizedFactors I).count P₂ with hc₂
    have hprod : I = P₁ ^ c₁ * P₂ ^ c₂ := by
      conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
      rw [Finset.prod_multiset_count,
        Finset.prod_subset (s₁ := (normalizedFactors I).toFinset) (s₂ := {P₁, P₂}) ?_ ?_,
        Finset.prod_pair hne]
      · intro Q hQ
        rcases hall Q (Multiset.mem_toFinset.mp hQ) with h | h <;> simp [h]
      · intro Q _ hQ
        rw [Multiset.mem_toFinset] at hQ
        rw [Multiset.count_eq_zero_of_notMem hQ, pow_zero]
    have hsum : c₁ + c₂ = k := by
      have := hI
      rw [hprod, map_mul, map_pow, map_pow, hN₁, hN₂, ← pow_add] at this
      exact Nat.pow_right_injective hp.out.two_le this
    have hk : k - c₁ = c₂ := by omega
    refine ⟨⟨c₁, by omega⟩, Subtype.ext ?_⟩
    show P₁ ^ c₁ * P₂ ^ (k - c₁) = I
    rw [hk, hprod]
  rw [← Nat.card_eq_of_bijective φ ⟨hinj, hsurj⟩, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The same, from `ncard (primesOver (p)) = 2` and inertia degrees `1`. -/
theorem card_absNorm_eq_pow_of_ncard_eq_two
    (h2 : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2)
    (hdeg : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1) (k : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = p ^ k} = k + 1 := by
  obtain ⟨P₁, P₂, hne, hS⟩ := Set.ncard_eq_two.mp h2
  have hP₁ : P₁ ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by rw [hS]; simp
  have hP₂ : P₂ ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by rw [hS]; simp
  have hN₁ : absNorm P₁ = p := by
    rw [absNorm_eq_pow_inertiaDeg_of_mem_primesOver p hP₁, hdeg P₁ hP₁, pow_one]
  have hN₂ : absNorm P₂ = p := by
    rw [absNorm_eq_pow_inertiaDeg_of_mem_primesOver p hP₂, hdeg P₂ hP₂, pow_one]
  exact card_absNorm_eq_pow_of_primesOver_eq_pair p hne hS hN₁ hN₂ k

end CN1.Epstein
