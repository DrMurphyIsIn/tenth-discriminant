import Mathlib
import CN1.Finite.SplitPrime
import CN1.Finite.Bridge
import HCN.Finite.NotRep

/-!
# HCN.Finite.ClassLower: the bridge-free lower bound `classNumber K ≥ 1 + Σ (1 + f_i)`

`K` is a number field with `𝓞 K = ℤ[θ]`, `θ² = t·θ - c`, given by CN-1's
interface `CN1.Finite.QuadInt K t c`; the norm form is `Q(x, y) = x² + t·x·y + c·y²` and `d = 4c - t² > 0`.

**The three-class lemma.** Let `p` be a prime with
* (a) `p ∤ d` and a root `r` of `X² - t·X + c` mod `p` (so `p` splits; `SplitW`),
* (b) `NotRep t c p`: `Q` does not represent `p`,
* (c) `NotRepYNonzero t c (p²)`: every solution of `Q(x, y) = p²` has `y = 0`.

Let `P` be a prime of norm `p` (Kummer-Dedekind, as in CN-1's `SplitPrime`). Then `1`, `[P]`, `[P]⁻¹` are pairwise
distinct:
* `[P] ≠ 1` (`mk0_ne_one`): a generator of `P` would have norm `p = Q(x, y)`, against (b).
* `[P]⁻¹` is the class of an ideal `J` of norm `p` (`exists_mul_eq_span_of_absNorm_eq`): `(p) ⊆ P`, so
  `(p) = P·J`, and `N(J) = p²/p = p`. No Kummer-Dedekind pair and no conjugation is needed for this.
* `[P] ≠ [P]⁻¹` (`mk0_ne_inv_self`): otherwise `P² = (β)` with `Q(β) = p²`, so `β = x ∈ ℤ` by (c) and `x = ±p`.
  Some `θ - z` (`z ∈ ℤ`, a root mod `p`) lies in `P` (`exists_sub_mem`), so `p ∣ (θ - z)² = (t - 2z)·θ + (z² - c)`,
  hence `p ∣ t - 2z`, hence `p ∣ (t - 2z)² - 4(z² - t z + c) = -d`, against (a).
  Only the direction "y = 0 ⇒ β ∈ ℤ" is used, so there is **no unit hypothesis**. For `d = 3, 4`, (c) is
  unsatisfiable (a unit times `p` has `y ≠ 0`), so the lemma is vacuous there. Conversely (not used): for `d > 4`,
  given (a), (c) fails iff `[P]² = 1`.

**The pair test.** For two chosen primes `p ≠ p'` with primes `P, P'`, `NotRep t c (p p')` gives exactly the
CROSS distinctness `{[P], [P]⁻¹} ∩ {[P'], [P']⁻¹} = ∅` (`mk0_ne_inv`: `[I] = [J]⁻¹` makes `I·J` principal, of norm
`N(I)·N(J)`). It says nothing about `≠ 1` (that is (b)) or about `[P] ≠ [P]⁻¹` (that is (c)).

**The certificate.** `ClassCert t c ps` for a list `ps` of CHOSEN primes `(p, r, f)` (`r` the root of (a),
`f` the inverse flag): (a) and (b) for every `p`, the pair test for every earlier/later pair, and (c) exactly for the
`p` with `f = true`. A skipped prime is simply absent and leaves no hypothesis; an order-2 prime (flag `false`)
contributes one class. Then `1 + weight ps ≤ classNumber K` with `weight ps = Σ (if f then 2 else 1)`
(`le_classNumber_of_cert`). A repeated prime cannot occur in a valid certificate: its pair test would be
`NotRep (p²)`, false since `Q(p, 0) = p²`; so no `Nodup` hypothesis is needed.

Mathlib's class-group steps: `ClassGroup.mk0_eq_one_iff` and `ClassGroup.mk0_eq_mk0_inv_iff`.
-/

open NumberField Ideal Module Polynomial
open scoped nonZeroDivisors

namespace HCN.Finite

open CN1.Finite (QuadInt)

variable {K : Type*} [Field K] [NumberField K]

/-! ### Kernel-decidable faces: primality and the split witness -/

/-- Trial-division primality, as a `Bool` (kernel-friendly; `p ≤ 71` here). -/
def primeB (p : ℕ) : Bool := decide (2 ≤ p) && (List.range p).all fun k => decide (k < 2) || p % k != 0

theorem primeB_sound {p : ℕ} (h : primeB p = true) : p.Prime := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h2, h⟩ := h
  rw [Nat.prime_def_lt']
  refine ⟨h2, fun k hk2 hkp hdvd => ?_⟩
  rcases h k hkp with h' | h'
  · omega
  · exact h' (Nat.mod_eq_zero_of_dvd hdvd)

/-- **The split witness (a)**: `p` prime, `p ∤ d = 4c - t²`, and `p ∣ r² - t·r + c`. -/
def SplitW (t c p r : ℕ) : Bool :=
  primeB p && (4 * c - t * t) % p != 0 && decide (t * r ≤ r * r + c) && (r * r + c - t * r) % p == 0

theorem SplitW.sound {t c p r : ℕ} (htc : t * t ≤ 4 * c) (h : SplitW t c p r = true) :
    p.Prime ∧ ¬ (p : ℤ) ∣ 4 * c - t * t ∧ (p : ℤ) ∣ (r : ℤ) ^ 2 - t * r + c := by
  simp only [SplitW, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hp, hd⟩, hle⟩, hr⟩ := h
  refine ⟨primeB_sound hp, ?_, ?_⟩
  · intro hdvd
    apply hd
    have : (p : ℤ) ∣ ((4 * c - t * t : ℕ) : ℤ) := by push_cast [Nat.cast_sub htc]; exact hdvd
    exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp this)
  · have h1 : p ∣ r * r + c - t * r := Nat.dvd_of_mod_eq_zero hr
    have h2 := Int.natCast_dvd_natCast.mpr h1
    push_cast [Nat.cast_sub hle] at h2
    convert h2 using 1
    ring

/-! ### The certificate -/

/-- `PairsOK t c p qs`: the pair test `NotRep t c (p·q)` against every prime `q` of `qs`. -/
def PairsOK (t c p : ℕ) : List (ℕ × ℕ × Bool) → Prop
  | [] => True
  | q :: qs => NotRep t c (p * q.1) ∧ PairsOK t c p qs

/-- **The certificate** for a list of chosen primes `(p, r, f)`: (a) the split witness, (b) `NotRep p`, the pair tests
against the later primes, and (c) `NotRepYNonzero (p²)` exactly when the inverse flag `f` is set. -/
def ClassCert (t c : ℕ) : List (ℕ × ℕ × Bool) → Prop
  | [] => True
  | q :: qs => SplitW t c q.1 q.2.1 = true ∧ NotRep t c q.1 ∧ PairsOK t c q.1 qs ∧
      (q.2.2 = true → NotRepYNonzero t c (q.1 ^ 2)) ∧ ClassCert t c qs

/-- The number of classes `≠ 1` that a certificate certifies: 2 per flagged prime, 1 per order-2 prime. -/
def weight : List (ℕ × ℕ × Bool) → ℕ
  | [] => 0
  | q :: qs => (if q.2.2 then 2 else 1) + weight qs

instance PairsOK.decidable (t c p : ℕ) : ∀ qs, Decidable (PairsOK t c p qs)
  | [] => isTrue trivial
  | _ :: qs =>
    haveI := PairsOK.decidable t c p qs
    inferInstanceAs (Decidable (_ ∧ _))

instance ClassCert.decidable (t c : ℕ) : ∀ ps, Decidable (ClassCert t c ps)
  | [] => isTrue trivial
  | q :: qs =>
    haveI := PairsOK.decidable t c q.1 qs
    haveI := ClassCert.decidable t c qs
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Builders, so that generated files can assemble a certificate from named hypotheses. -/
theorem PairsOK.nil (t c p : ℕ) : PairsOK t c p [] := trivial

theorem PairsOK.cons {t c p : ℕ} {q : ℕ × ℕ × Bool} {qs : List (ℕ × ℕ × Bool)}
    (h : NotRep t c (p * q.1)) (hs : PairsOK t c p qs) : PairsOK t c p (q :: qs) := ⟨h, hs⟩

theorem ClassCert.nil (t c : ℕ) : ClassCert t c [] := trivial

theorem ClassCert.cons {t c p r : ℕ} {f : Bool} {qs : List (ℕ × ℕ × Bool)}
    (ha : SplitW t c p r = true) (hb : NotRep t c p) (hx : PairsOK t c p qs)
    (hc : f = true → NotRepYNonzero t c (p ^ 2)) (hs : ClassCert t c qs) :
    ClassCert t c ((p, r, f) :: qs) := ⟨ha, hb, hx, hc, hs⟩

theorem PairsOK.mem {t c p : ℕ} : ∀ {qs : List (ℕ × ℕ × Bool)}, PairsOK t c p qs →
    ∀ q ∈ qs, NotRep t c (p * q.1)
  | [], _, q, hq => by simp at hq
  | _ :: _, ⟨h, hs⟩, q, hq => by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h
    · exact PairsOK.mem hs q hq

/-! ### Ideals of `𝓞 K = ℤ[θ]` -/

section QuadInt

theorem four_c_sub_t_sq_nonneg {t c : ℕ} (htc : t * t ≤ 4 * c) : (0 : ℤ) ≤ 4 * c - (t : ℤ) ^ 2 := by
  have : ((t * t : ℕ) : ℤ) ≤ ((4 * c : ℕ) : ℤ) := by exact_mod_cast htc
  push_cast at this
  nlinarith

variable {t c : ℕ} (D : QuadInt K (t : ℤ) (c : ℤ))
include D

/-- `N(n) = n²` for `n ∈ ℤ`. -/
theorem norm_intCast (n : ℤ) : Algebra.norm ℤ (n : 𝓞 K) = n ^ 2 := by
  have h := D.norm_eq n 0
  simpa using h

/-- `θ² = t·θ - c` in `𝓞 K`. -/
theorem theta_sq : D.θ ^ 2 = (t : 𝓞 K) * D.θ - (c : 𝓞 K) := by
  have h := minpoly.aeval ℤ D.θ
  rw [D.minpoly_eq] at h
  simp only [map_add, map_sub, map_mul, map_pow, aeval_X, map_natCast] at h
  linear_combination h

/-- The coordinates in the `ℤ`-basis `1, θ` are unique (`d > 0`). -/
theorem add_mul_theta_inj (htc : t * t < 4 * c) {a b a' b' : ℤ}
    (h : (a : 𝓞 K) + (b : 𝓞 K) * D.θ = (a' : 𝓞 K) + (b' : 𝓞 K) * D.θ) : a = a' ∧ b = b' := by
  have h0 : ((a - a' : ℤ) : 𝓞 K) + ((b - b' : ℤ) : 𝓞 K) * D.θ = 0 := by
    push_cast; linear_combination h
  have hn := congrArg (Algebra.norm ℤ) h0
  rw [D.norm_eq, Algebra.norm_zero] at hn
  have h4 := CN1.Finite.four_mul_form (t : ℤ) c (a - a') (b - b')
  have hd : (0 : ℤ) < 4 * c - (t : ℤ) ^ 2 := by
    have : ((t * t : ℕ) : ℤ) < ((4 * c : ℕ) : ℤ) := by exact_mod_cast htc
    push_cast at this
    nlinarith
  rw [hn] at h4
  have hb : (b - b') ^ 2 = 0 := by
    have : (4 * c - (t : ℤ) ^ 2) * (b - b') ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * (a - a') + t * (b - b')), sq_nonneg (b - b')]
    exact (mul_eq_zero.mp this).resolve_left hd.ne'
  have hb' : b - b' = 0 := pow_eq_zero_iff two_ne_zero |>.mp hb
  rw [hb'] at h4
  have ha : (2 * (a - a')) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * (a - a'))]
  have ha' : 2 * (a - a') = 0 := pow_eq_zero_iff two_ne_zero |>.mp ha
  constructor <;> omega

/-- `absNorm (span {β}) = |N β|` is a value of `Q`, at the coordinates of `β`. -/
theorem exists_form_eq_absNorm_span (htc : t * t ≤ 4 * c) (β : 𝓞 K) :
    ∃ x y : ℤ, β = (x : 𝓞 K) + (y : 𝓞 K) * D.θ ∧
      x ^ 2 + (t : ℤ) * x * y + (c : ℤ) * y ^ 2 = (absNorm (span {β}) : ℤ) := by
  obtain ⟨x, y, rfl⟩ := D.exists_eq_add_mul β
  refine ⟨x, y, rfl, ?_⟩
  rw [absNorm_span_singleton, D.norm_eq, Int.natCast_natAbs, abs_of_nonneg]
  exact CN1.Finite.form_nonneg (four_c_sub_t_sq_nonneg htc) x y

/-- **(b) ⇒ `[I] ≠ 1`.** If `Q` does not represent `N(I)`, then `I` is not principal. -/
theorem mk0_ne_one (htc : t * t ≤ 4 * c) (I : (Ideal (𝓞 K))⁰)
    (h : NotRep t c (absNorm (I : Ideal (𝓞 K)))) : ClassGroup.mk0 I ≠ 1 := by
  obtain ⟨I, hI⟩ := I
  rw [Ne, ClassGroup.mk0_eq_one_iff hI]
  rintro ⟨β, hβ⟩
  have h' : NotRep t c (absNorm I) := h
  rw [hβ, Ideal.submodule_span_eq] at h'
  obtain ⟨x, y, -, hxy⟩ := exists_form_eq_absNorm_span D htc β
  exact NotRep.sound htc h' x y hxy

/-- **The pair test ⇒ `[I] ≠ [J]⁻¹`.** If `Q` does not represent `N(I)·N(J)`, then `I·J` is not principal. -/
theorem mk0_ne_inv (htc : t * t ≤ 4 * c) (I J : (Ideal (𝓞 K))⁰)
    (h : NotRep t c (absNorm (I : Ideal (𝓞 K)) * absNorm (J : Ideal (𝓞 K)))) :
    ClassGroup.mk0 I ≠ (ClassGroup.mk0 J)⁻¹ := by
  rw [Ne, ClassGroup.mk0_eq_mk0_inv_iff]
  rintro ⟨β, -, hβ⟩
  rw [← map_mul, hβ] at h
  obtain ⟨x, y, -, hxy⟩ := exists_form_eq_absNorm_span D htc β
  exact NotRep.sound htc h x y hxy

/-- **A prime of norm `p`** from a root of `X² - t·X + c` mod `p` (Kummer-Dedekind; CN-1's `SplitPrime`
argument). -/
theorem exists_absNorm_eq_of_root {p : ℕ} (hp : p.Prime) (r : ℤ)
    (hr : (p : ℤ) ∣ r ^ 2 - t * r + c) : ∃ P : Ideal (𝓞 K), absNorm P = p := by
  haveI := Fact.mk hp
  have hexp : ¬ p ∣ RingOfIntegers.exponent D.θ := by
    rw [RingOfIntegers.exponent_eq_one_iff.mpr D.adjoin_eq_top]
    exact hp.not_dvd_one
  have hmap0 : (minpoly ℤ D.θ).map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_monic_ne_zero (minpoly.monic D.θ.isIntegral)
  have hQ : (X - C r).map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod D.θ p := by
    rw [RingOfIntegers.monicFactorsMod, Multiset.mem_toFinset,
      Polynomial.mem_normalizedFactors_iff hmap0, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, ?_⟩
    rw [dvd_iff_isRoot, D.minpoly_eq]
    have hr' : ((r ^ 2 - t * r + c : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hr
    simp only [IsRoot.def, eval_map, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X,
      eval₂_C]
    simp only [eq_intCast]
    push_cast at hr' ⊢
    linear_combination hr'
  set P : Ideal (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩ : Ideal (𝓞 K)) with hPdef
  have hPmem : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) :=
    ((Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm ⟨_, hQ⟩).prop
  haveI hPprime : P.IsPrime := hPmem.1
  haveI hPlies : P.LiesOver (span {(p : ℤ)}) := hPmem.2
  have hdeg1 : P.inertiaDeg ℤ = 1 := by
    rw [hPdef, Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply hexp hQ,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, natDegree_X_sub_C]
  exact ⟨P, by rw [← Ideal.pow_inertiaDeg p P, hdeg1, pow_one]⟩

/-- **The inverse class has a representative of norm `p`.** For `N(P) = p` prime: `(p) ⊆ P`, so `(p) = P·J` with
`N(J) = p`. (No Kummer-Dedekind pair is needed; for split `p`, `J` is the conjugate prime.) -/
theorem exists_mul_eq_span_of_absNorm_eq {P : Ideal (𝓞 K)} {p : ℕ} (hp : p.Prime) (hP : absNorm P = p) :
    ∃ J : Ideal (𝓞 K), absNorm J = p ∧ P * J = span {(p : 𝓞 K)} := by
  have hmem : (p : 𝓞 K) ∈ P := by have := absNorm_mem P; rwa [hP] at this
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr ((span_singleton_le_iff_mem P).mpr hmem)
  refine ⟨J, ?_, hJ.symm⟩
  have h := congrArg absNorm hJ
  rw [map_mul, hP, absNorm_span_singleton, show (p : 𝓞 K) = ((p : ℤ) : 𝓞 K) by simp,
    norm_intCast D, Int.natAbs_pow, Int.natAbs_natCast] at h
  have hp0 := hp.pos
  have : p * p = p * absNorm J := by rw [← sq]; exact h
  exact (Nat.eq_of_mul_eq_mul_left hp0 this).symm

/-- An integer in an ideal of prime norm `p` is divisible by `p`. -/
theorem dvd_of_intCast_mem {P : Ideal (𝓞 K)} {p : ℕ} (hp : p.Prime) (hP : absNorm P = p) {n : ℤ}
    (hn : (n : 𝓞 K) ∈ P) : (p : ℤ) ∣ n := by
  have h := absNorm_dvd_norm_of_mem hn
  rw [hP, norm_intCast D] at h
  exact (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow h

/-- **The residue of `θ`.** For `N(P) = p` prime, `θ ≡ z (mod P)` for some `z ∈ ℤ`: `𝓞 K ⧸ P` has `p`
elements, so it is the image of `ZMod p`. -/
theorem exists_sub_mem {P : Ideal (𝓞 K)} {p : ℕ} (hp : p.Prime) (hP : absNorm P = p) :
    ∃ z : ℤ, D.θ - (z : 𝓞 K) ∈ P := by
  haveI := Fact.mk hp
  have hne : P ≠ ⊥ := by
    intro h; rw [h, absNorm_bot] at hP; exact hp.ne_zero hP.symm
  haveI hprime : P.IsPrime := isPrime_of_irreducible_absNorm (by rw [hP]; exact hp)
  haveI : P.IsMaximal := hprime.isMaximal hne
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← absNorm_apply, hP]
  haveI : CharP (𝓞 K ⧸ P) p := charP_of_card_eq_prime hcard
  let f : ZMod p →+* 𝓞 K ⧸ P := ZMod.castHom dvd_rfl _
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by rw [ZMod.card, hcard]⟩
  obtain ⟨z, hz⟩ := hf.2 (Ideal.Quotient.mk P D.θ)
  refine ⟨(z.val : ℤ), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hz, map_intCast, Int.cast_natCast]
  simp only [f, ZMod.castHom_apply, ZMod.natCast_val, sub_self]

/-- If `θ - z ∈ P` with `N(P) = p` prime, then `z` is a root of `X² - t·X + c` mod `p`. -/
theorem dvd_root_of_sub_mem {P : Ideal (𝓞 K)} {p : ℕ} (hp : p.Prime) (hP : absNorm P = p) {z : ℤ}
    (hz : D.θ - (z : 𝓞 K) ∈ P) : (p : ℤ) ∣ z ^ 2 - t * z + c := by
  apply dvd_of_intCast_mem D hp hP
  have h : ((z ^ 2 - t * z + c : ℤ) : 𝓞 K) = -(D.θ - z) * (D.θ + z - t) := by
    push_cast
    linear_combination theta_sq D
  rw [h, neg_mul]
  exact P.neg_mem (P.mul_mem_right _ hz)

/-- **(c) ⇒ `[P] ≠ [P]⁻¹`**, for a prime of norm `p ∤ d`. No unit hypothesis. -/
theorem mk0_ne_inv_self (htc : t * t < 4 * c) (P : (Ideal (𝓞 K))⁰) {p : ℕ} (hp : p.Prime)
    (hP : absNorm (P : Ideal (𝓞 K)) = p) (hpd : ¬ (p : ℤ) ∣ 4 * c - t * t)
    (hY : NotRepYNonzero t c (p ^ 2)) : ClassGroup.mk0 P ≠ (ClassGroup.mk0 P)⁻¹ := by
  rw [Ne, ClassGroup.mk0_eq_mk0_inv_iff]
  rintro ⟨β, -, hβ⟩
  obtain ⟨x, y, rfl, hxy⟩ := exists_form_eq_absNorm_span D htc.le β
  rw [← hβ, map_mul, hP] at hxy
  have hy : y = 0 := NotRepYNonzero.sound htc.le hY x y (by rw [hxy]; push_cast; ring)
  subst hy
  obtain ⟨z, hz⟩ := exists_sub_mem D hp hP
  have hz2 : (D.θ - z) ^ 2 ∈ (P : Ideal (𝓞 K)) * P := by rw [sq]; exact Ideal.mul_mem_mul hz hz
  rw [hβ, Ideal.mem_span_singleton] at hz2
  obtain ⟨γ, hγ⟩ := hz2
  obtain ⟨a, b, rfl⟩ := D.exists_eq_add_mul γ
  have key : ((z ^ 2 - c : ℤ) : 𝓞 K) + ((t - 2 * z : ℤ) : 𝓞 K) * D.θ =
      ((x * a : ℤ) : 𝓞 K) + ((x * b : ℤ) : 𝓞 K) * D.θ := by
    push_cast at hγ ⊢
    linear_combination hγ - theta_sq D
  obtain ⟨-, hb⟩ := add_mul_theta_inj D htc key
  -- `x² = p²`, so `p ∣ x`
  have hx2 : x ^ 2 = (p : ℤ) ^ 2 := by push_cast at hxy; linear_combination hxy
  have hpx : (p : ℤ) ∣ x :=
    (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow (show (p : ℤ) ∣ x ^ 2 from hx2 ▸ dvd_pow_self _ two_ne_zero)
  have h1 : (p : ℤ) ∣ t - 2 * z := hb ▸ dvd_mul_of_dvd_left hpx b
  have h2 : (p : ℤ) ∣ z ^ 2 - t * z + c := dvd_root_of_sub_mem D hp hP hz
  apply hpd
  have : 4 * (c : ℤ) - t * t = 4 * (z ^ 2 - t * z + c) - (t - 2 * z) ^ 2 := by ring
  rw [this]
  exact dvd_sub (dvd_mul_of_dvd_right h2 4) (dvd_pow h1 two_ne_zero)

omit D in
theorem mem_nonZeroDivisors_of_absNorm_eq {I : Ideal (𝓞 K)} {p : ℕ} (hp : p.Prime) (hI : absNorm I = p) :
    I ∈ (Ideal (𝓞 K))⁰ :=
  mem_nonZeroDivisors_of_ne_zero (by
    intro h; rw [h, Submodule.zero_eq_bot, absNorm_bot] at hI; exact hp.ne_zero hI.symm)

/-- **The certified classes.** A valid certificate yields `weight ps` classes, none of them `1`, each the class (or
its inverse) of an ideal whose norm is one of the chosen primes. -/
theorem exists_classes_of_cert (htc : t * t < 4 * c) : ∀ ps : List (ℕ × ℕ × Bool), ClassCert t c ps →
    ∃ S : Finset (ClassGroup (𝓞 K)), S.card = weight ps ∧ (1 : ClassGroup (𝓞 K)) ∉ S ∧
      ∀ g ∈ S, ∃ q ∈ ps, ∃ I : (Ideal (𝓞 K))⁰, absNorm (I : Ideal (𝓞 K)) = q.1 ∧
        (g = ClassGroup.mk0 I ∨ g = (ClassGroup.mk0 I)⁻¹)
  | [], _ => ⟨∅, rfl, by simp, by simp⟩
  | (p, r, f) :: qs, ⟨hs, hn, hpairs, hf, hrest⟩ => by
    classical
    obtain ⟨S, hcard, h1, hmemS⟩ := exists_classes_of_cert htc qs hrest
    obtain ⟨hp, hpd, hr⟩ := SplitW.sound htc.le hs
    obtain ⟨P0, hP0⟩ := exists_absNorm_eq_of_root D hp r hr
    obtain ⟨J0, hJ0, hPJ⟩ := exists_mul_eq_span_of_absNorm_eq D hp hP0
    let P : (Ideal (𝓞 K))⁰ := ⟨P0, mem_nonZeroDivisors_of_absNorm_eq hp hP0⟩
    let J : (Ideal (𝓞 K))⁰ := ⟨J0, mem_nonZeroDivisors_of_absNorm_eq hp hJ0⟩
    have hPn : absNorm (P : Ideal (𝓞 K)) = p := hP0
    have hJn : absNorm (J : Ideal (𝓞 K)) = p := hJ0
    have hJinv : ClassGroup.mk0 J = (ClassGroup.mk0 P)⁻¹ :=
      ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨p, by exact_mod_cast hp.ne_zero, by
        show J0 * P0 = _; rw [mul_comm]; exact hPJ⟩
    have hg1 : ClassGroup.mk0 P ≠ 1 := mk0_ne_one D htc.le P (by rw [hPn]; exact hn)
    have hcross : ∀ h ∈ S, ClassGroup.mk0 P ≠ h ∧ (ClassGroup.mk0 P)⁻¹ ≠ h := by
      intro h hh
      obtain ⟨q, hq, I, hI, hcase⟩ := hmemS h hh
      have hnr : NotRep t c (p * q.1) := PairsOK.mem hpairs q hq
      rcases hcase with rfl | rfl
      · constructor
        · intro heq
          apply mk0_ne_inv D htc.le J I (by rw [hJn, hI]; exact hnr)
          rw [hJinv, heq]
        · intro heq
          exact mk0_ne_inv D htc.le I P (by rw [hI, hPn, mul_comm]; exact hnr) heq.symm
      · constructor
        · exact mk0_ne_inv D htc.le P I (by rw [hPn, hI]; exact hnr)
        · intro heq
          apply mk0_ne_inv D htc.le J I (by rw [hJn, hI]; exact hnr)
          rw [hJinv, inv_inj.mp heq]
    let T : Finset (ClassGroup (𝓞 K)) :=
      if f then {ClassGroup.mk0 P, (ClassGroup.mk0 P)⁻¹} else {ClassGroup.mk0 P}
    have hT : ∀ g ∈ T, g = ClassGroup.mk0 P ∨ (f = true ∧ g = (ClassGroup.mk0 P)⁻¹) := by
      intro g hg
      cases f
      · simp only [T, Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton] at hg
        exact Or.inl hg
      · simp only [T, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with hg | hg
        · exact Or.inl hg
        · exact Or.inr ⟨rfl, hg⟩
    have hdisj : Disjoint T S := by
      rw [Finset.disjoint_left]
      intro g hgT hgS
      rcases hT g hgT with rfl | ⟨-, rfl⟩
      · exact (hcross _ hgS).1 rfl
      · exact (hcross _ hgS).2 rfl
    have hTcard : T.card = if f then 2 else 1 := by
      cases f
      · simp [T]
      · have hne : ClassGroup.mk0 P ≠ (ClassGroup.mk0 P)⁻¹ :=
          mk0_ne_inv_self D htc P hp hPn (by exact_mod_cast hpd) (hf rfl)
        simp only [T, ↓reduceIte]
        exact Finset.card_pair hne
    refine ⟨T ∪ S, ?_, ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint hdisj, hTcard, hcard]
      rfl
    · rw [Finset.mem_union, not_or]
      refine ⟨fun h1T => ?_, h1⟩
      rcases hT 1 h1T with h | ⟨-, h⟩
      · exact hg1 h.symm
      · exact hg1 (inv_eq_one.mp h.symm)
    · intro g hg
      rcases Finset.mem_union.mp hg with hgT | hgS
      · refine ⟨(p, r, f), List.mem_cons_self, P, hPn, ?_⟩
        rcases hT g hgT with h | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr h
      · obtain ⟨q, hq, I, hI, hcase⟩ := hmemS g hgS
        exact ⟨q, List.mem_cons_of_mem _ hq, I, hI, hcase⟩

/-- **ClassLower.** A valid certificate of chosen primes gives `classNumber K ≥ 1 + weight ps`. -/
theorem le_classNumber_of_cert (htc : t * t < 4 * c) {ps : List (ℕ × ℕ × Bool)} (h : ClassCert t c ps) :
    1 + weight ps ≤ classNumber K := by
  classical
  obtain ⟨S, hS, h1, -⟩ := exists_classes_of_cert D htc ps h
  have hle := Finset.card_le_univ (insert 1 S)
  rw [Finset.card_insert_of_notMem h1, hS] at hle
  unfold classNumber
  omega

/-- **ClassLower, the `h ≥ 3` form** used for the class-number-two theorem. -/
theorem three_le_classNumber_of_cert (htc : t * t < 4 * c) {ps : List (ℕ × ℕ × Bool)} (h : ClassCert t c ps)
    (hw : 2 ≤ weight ps) : 3 ≤ classNumber K := by
  have := le_classNumber_of_cert D htc h
  omega

end QuadInt

/-! ### On CN-1's foundations -/

open CN1.Finite in
theorem tOf_mul_lt_four_mul_cOf {m : ℕ} (hm : m ≠ 0) : tOf m * tOf m < 4 * cOf m := by
  have h := four_mul_cOf m
  have hd : 0 < dOf m := by unfold dOf; split_ifs <;> omega
  rw [h, sq]
  omega

open CN1.Finite in
/-- **ClassLower on CN-1's foundations.** For `K` of degree two containing `√-m`, `m` squarefree, a valid certificate
for the principal form of `m` gives `classNumber K ≥ 1 + weight ps`. -/
theorem le_classNumber_of_cert_foundations (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) {ps : List (ℕ × ℕ × Bool)} (h : ClassCert (tOf m) (cOf m) ps) :
    1 + weight ps ≤ classNumber K := by
  obtain ⟨α, hα⟩ := hsq
  exact le_classNumber_of_cert (quadIntOfFoundations hK hm hα) (tOf_mul_lt_four_mul_cOf hm.ne_zero) h

end HCN.Finite
