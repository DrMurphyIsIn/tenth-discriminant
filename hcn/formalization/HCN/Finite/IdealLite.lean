import Mathlib
import CN1.Finite.Converse
import CN1.Finite.Bridge
import HCN.Finite.ClassLower
import HCN.Finite.Generation

/-!
# HCN.Finite.IdealLite: the bridge-lite, `classNumber K = 2` from explicit positive witnesses

For the 18 fields with `h = 2` we need an UPPER bound. The route:
1. (`Generation.lean`) every class contains a product of primes of norm at most the Minkowski bound
   `M ≤ (2/3)√d` (CN-1's `le_two_thirds_sqrt_of_le_minkowski`), so it suffices to place the class of each such prime
   in `{1, g}` for one class `g` with `g² = 1`.
2. A prime `I` of norm `q` (prime) has a residue: `θ - z ∈ I` for a root `z` of `X² - t·X + c` mod `q`
   (`exists_residue`), and **the residue determines the ideal** (`eq_of_sub_mem`: two ideals of norm `q` containing
   the same `θ - z` are equal, else `(q) = I·I' = I ∩ I' ∋ θ - z`, impossible in the basis `1, θ`). So the primes of
   norm `q` are the ideals "`(q, θ - z)`", one per root `z`, and positive witnesses can name them by `(q, z)`.
   (The other primes below the bound are inert, `I = (q)`, principal: CN-1's `absNorm_maximal_cases`.)
3. Positive witnesses (`β = x + y·θ`): `β ∈ I` iff `q ∣ x + y·z` (`add_mul_mem_of_dvd`); with `N(β) = N(I)`,
   `I = (β)` (`span_eq_of_witness`). For the class `g = [P₀]` of a prime of norm `q₀ ≠ q`, a `β ∈ I ∩ P₀ = I·P₀` of
   norm `q·q₀` gives `I·P₀ = (β)`, so `[I] = g⁻¹` (`mul_eq_span_of_witness`).
4. `g² = 1` when `X² - t·X + c` has a UNIQUE root `z₀` mod `q₀` (`q₀` ramified): the ideal `J₀` with `P₀·J₀ = (q₀)` has
   norm `q₀` and residue `z₀`, so `J₀ = P₀` by step 2.

This is a "half bridge" from ideals to norm forms, with no reduction theory and no composition. It avoids one
mechanism that would also work: the explicit ideals `span {N, r + ω}` and their norms via
`natAbs_det_basis_change` are not needed, because step 2 identifies each prime of norm `q` by its residue, and all
norms come from `absNorm_span_singleton` and `absNorm (I·J) = absNorm I · absNorm J`.

The per-field data is one decidable `BridgeCert` (all checks by the kernel), plus `NotRep t c q₀` for `g ≠ 1`.
-/

open NumberField NumberField.InfinitePlace Ideal Module Real
open scoped nonZeroDivisors

namespace HCN.Finite

open CN1.Finite (QuadInt)

variable {K : Type*} [Field K] [NumberField K]

/-! ### The decidable faces -/

/-- `z` is a root of `X² - t·X + c` mod `q`. -/
def rootB (t c q z : ℕ) : Bool := ((z : ℤ) ^ 2 - t * z + c) % q == 0

/-- `primeB` is complete. -/
theorem primeB_of_prime {p : ℕ} (hp : p.Prime) : primeB p = true := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨hp.two_le, fun k hk => ?_⟩
  by_cases hk2 : k < 2
  · exact Or.inl hk2
  · right
    intro h0
    have hdvd : k ∣ p := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.dvd_prime hp).mp hdvd with h | h <;> omega

theorem rootB_iff {t c q z : ℕ} : rootB t c q z = true ↔ (q : ℤ) ∣ (z : ℤ) ^ 2 - t * z + c := by
  simp only [rootB, beq_iff_eq]
  exact ⟨Int.dvd_of_emod_eq_zero, Int.emod_eq_zero_of_dvd⟩

/-- The principal form, over `ℤ`. -/
def formZ (t c : ℕ) (x y : ℤ) : ℤ := x ^ 2 + t * x * y + c * y ^ 2

/-- A positive witness for the prime "`(q, θ - z)`": `β = x + y·θ` with `q ∣ x + y·z`, and either `N(β) = q`
(`g = false`: the prime is principal) or `N(β) = q·q₀` and `q₀ ∣ x + y·z₀` (`g = true`: its class is `[P₀]⁻¹`). -/
structure BWit where
  q : ℕ
  z : ℕ
  x : ℤ
  y : ℤ
  g : Bool

/-- The check of one witness against the prime `(q, z)`. -/
def witOK (t c q0 z0 q z : ℕ) (w : BWit) : Bool :=
  w.q == q && w.z == z && (w.x + w.y * z) % q == 0 &&
    (if w.g then formZ t c w.x w.y == q * q0 && (w.x + w.y * z0) % q0 == 0 && q != q0
     else formZ t c w.x w.y == q)

/-- **The bridge certificate.** `q₀` prime with the unique root `z₀ < q₀` mod `q₀`, and every root `z` mod every prime
`q < B` is either `(q₀, z₀)` or carries a valid witness. -/
def BridgeCert (t c B q0 z0 : ℕ) (W : List BWit) : Bool :=
  primeB q0 && decide (z0 < q0) && rootB t c q0 z0 &&
    (List.range q0).all (fun z => !rootB t c q0 z || z == z0) &&
    (List.range B).all (fun q => !primeB q ||
      (List.range q).all (fun z => !rootB t c q z || q == q0 || W.any (witOK t c q0 z0 q z)))

/-! ### Ideals named by their residue -/

section QuadInt

variable {t c : ℕ} (D : QuadInt K (t : ℤ) (c : ℤ))
include D

omit D in
theorem natCast_mem_of_absNorm_eq' {I : Ideal (𝓞 K)} {q : ℕ} (hI : absNorm I = q) : (q : 𝓞 K) ∈ I := by
  have := absNorm_mem I; rwa [hI] at this

omit D in
theorem eq_of_le_of_absNorm_eq {I J : Ideal (𝓞 K)} (hle : I ≤ J) (h : absNorm I = absNorm J)
    (h0 : absNorm J ≠ 0) : I = J := by
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr hle
  have hn := congrArg absNorm hL
  rw [map_mul, h] at hn
  have hL1 : absNorm L = 1 := by
    have : absNorm J * absNorm L = absNorm J * 1 := by rw [mul_one]; exact hn.symm
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) this
  rw [absNorm_eq_one_iff] at hL1
  rw [hL, hL1, mul_top]

omit D in
theorem isMaximal_of_absNorm_eq {I : Ideal (𝓞 K)} {q : ℕ} (hq : q.Prime) (hI : absNorm I = q) :
    I.IsMaximal := by
  have hne : I ≠ ⊥ := by intro h; rw [h, absNorm_bot] at hI; exact hq.ne_zero hI.symm
  have hprime : I.IsPrime := isPrime_of_irreducible_absNorm (by rw [hI]; exact hq)
  exact hprime.isMaximal hne

/-- `β = x + y·θ ∈ I` when `θ - z ∈ I` and `q = N(I)` divides `x + y·z`. -/
theorem add_mul_mem_of_dvd {I : Ideal (𝓞 K)} {q : ℕ} (hI : absNorm I = q) {z : ℤ} (hz : D.θ - (z : 𝓞 K) ∈ I)
    {x y : ℤ} (h : (q : ℤ) ∣ x + y * z) : (x : 𝓞 K) + (y : 𝓞 K) * D.θ ∈ I := by
  obtain ⟨k, hk⟩ := h
  have hq : ((q : ℤ) : 𝓞 K) ∈ I := by simpa using natCast_mem_of_absNorm_eq' hI
  have hk' : ((x + y * z : ℤ) : 𝓞 K) = ((q * k : ℤ) : 𝓞 K) := by rw [hk]
  have heq : (x : 𝓞 K) + (y : 𝓞 K) * D.θ = ((q : ℤ) : 𝓞 K) * (k : 𝓞 K) + (y : 𝓞 K) * (D.θ - z) := by
    push_cast at hk' ⊢
    linear_combination hk'
  rw [heq]
  exact I.add_mem (I.mul_mem_right _ hq) (I.mul_mem_left _ hz)

/-- The residue can be changed modulo `q`. -/
theorem sub_mem_of_dvd {I : Ideal (𝓞 K)} {q : ℕ} (hI : absNorm I = q) {z z' : ℤ}
    (hz : D.θ - (z : 𝓞 K) ∈ I) (h : (q : ℤ) ∣ z - z') : D.θ - (z' : 𝓞 K) ∈ I := by
  obtain ⟨k, hk⟩ := h
  have hq : ((q : ℤ) : 𝓞 K) ∈ I := by simpa using natCast_mem_of_absNorm_eq' hI
  have hk' : ((z - z' : ℤ) : 𝓞 K) = ((q * k : ℤ) : 𝓞 K) := by rw [hk]
  have heq : D.θ - (z' : 𝓞 K) = (D.θ - z) + ((q : ℤ) : 𝓞 K) * (k : 𝓞 K) := by
    push_cast at hk' ⊢
    linear_combination hk'
  rw [heq]
  exact I.add_mem hz (I.mul_mem_right _ hq)

/-- **The residue of `θ`, reduced.** An ideal of prime norm `q` contains `θ - z` for a root `z < q` of
`X² - t·X + c` mod `q`. -/
theorem exists_residue {I : Ideal (𝓞 K)} {q : ℕ} (hq : q.Prime) (hI : absNorm I = q) :
    ∃ z : ℕ, z < q ∧ rootB t c q z = true ∧ D.θ - ((z : ℤ) : 𝓞 K) ∈ I := by
  obtain ⟨z, hz⟩ := exists_sub_mem D hq hI
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hnn : 0 ≤ z % (q : ℤ) := Int.emod_nonneg z hq0.ne'
  have hlt : z % (q : ℤ) < q := Int.emod_lt_of_pos z hq0
  refine ⟨(z % (q : ℤ)).toNat, by omega, ?_, ?_⟩
  · have hz' : D.θ - (((z % (q : ℤ)).toNat : ℤ) : 𝓞 K) ∈ I := by
      apply sub_mem_of_dvd D hI hz
      rw [Int.toNat_of_nonneg hnn]
      exact ⟨z / q, by rw [Int.emod_def]; ring⟩
    exact rootB_iff.mpr (dvd_root_of_sub_mem D hq hI hz')
  · apply sub_mem_of_dvd D hI hz
    rw [Int.toNat_of_nonneg hnn]
    exact ⟨z / q, by rw [Int.emod_def]; ring⟩

/-- **The residue determines the ideal.** Two ideals of prime norm `q` containing the same `θ - z` are equal. -/
theorem eq_of_sub_mem (htc : t * t < 4 * c) {I I' : Ideal (𝓞 K)} {q : ℕ} (hq : q.Prime) (hI : absNorm I = q)
    (hI' : absNorm I' = q) {z : ℤ} (hz : D.θ - (z : 𝓞 K) ∈ I) (hz' : D.θ - (z : 𝓞 K) ∈ I') : I = I' := by
  by_contra hne
  have hcop : I ⊔ I' = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne (isMaximal_of_absNorm_eq hq hI) (isMaximal_of_absNorm_eq hq hI') hne
  have hspan : span {(q : 𝓞 K)} = I * I' := by
    apply eq_of_le_of_absNorm_eq
    · rw [mul_eq_inf_of_coprime hcop, span_singleton_le_iff_mem]
      exact ⟨natCast_mem_of_absNorm_eq' hI, natCast_mem_of_absNorm_eq' hI'⟩
    · rw [map_mul, hI, hI', absNorm_span_singleton, show (q : 𝓞 K) = ((q : ℤ) : 𝓞 K) by simp,
        norm_intCast D, Int.natAbs_pow, Int.natAbs_natCast, sq]
    · rw [map_mul, hI, hI']; exact mul_ne_zero hq.ne_zero hq.ne_zero
  have hmem : D.θ - (z : 𝓞 K) ∈ span {(q : 𝓞 K)} := by
    rw [hspan, mul_eq_inf_of_coprime hcop]; exact ⟨hz, hz'⟩
  rw [mem_span_singleton] at hmem
  obtain ⟨γ, hγ⟩ := hmem
  obtain ⟨a, b, rfl⟩ := D.exists_eq_add_mul γ
  have key : ((-z : ℤ) : 𝓞 K) + ((1 : ℤ) : 𝓞 K) * D.θ = ((q * a : ℤ) : 𝓞 K) + ((q * b : ℤ) : 𝓞 K) * D.θ := by
    push_cast
    linear_combination hγ
  obtain ⟨-, h1⟩ := add_mul_theta_inj D htc key
  have h2 := hq.two_le
  have : (q : ℤ) * b = 1 := h1.symm
  have hq1 : (q : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) this
  omega

/-- **Positive witness, principal.** If `θ - z ∈ I`, `N(I) = q`, `Q(x, y) = q` and `q ∣ x + y·z`, then
`I = (x + y·θ)`. -/
theorem span_eq_of_witness {I : Ideal (𝓞 K)} {q : ℕ} (hq : q.Prime) (hI : absNorm I = q)
    {z : ℤ} (hz : D.θ - (z : 𝓞 K) ∈ I) {x y : ℤ} (hQ : x ^ 2 + (t : ℤ) * x * y + (c : ℤ) * y ^ 2 = q)
    (hdvd : (q : ℤ) ∣ x + y * z) : span {(x : 𝓞 K) + (y : 𝓞 K) * D.θ} = I := by
  apply eq_of_le_of_absNorm_eq
  · rw [span_singleton_le_iff_mem]; exact add_mul_mem_of_dvd D hI hz hdvd
  · rw [hI, absNorm_span_singleton, D.norm_eq, hQ, Int.natAbs_natCast]
  · rw [hI]; exact hq.ne_zero

/-- **Positive witness, the class `g⁻¹`.** For ideals `I, P` of distinct prime norms `q, q₀`, with `θ - z ∈ I`,
`θ - z₀ ∈ P`, `Q(x, y) = q·q₀`, `q ∣ x + y·z` and `q₀ ∣ x + y·z₀`: `I·P = (x + y·θ)`. -/
theorem mul_eq_span_of_witness {I P : Ideal (𝓞 K)} {q q0 : ℕ} (hq : q.Prime) (hq0 : q0.Prime) (hqq : q ≠ q0)
    (hI : absNorm I = q) (hP : absNorm P = q0) {z z0 : ℤ} (hz : D.θ - (z : 𝓞 K) ∈ I)
    (hz0 : D.θ - (z0 : 𝓞 K) ∈ P) {x y : ℤ} (hQ : x ^ 2 + (t : ℤ) * x * y + (c : ℤ) * y ^ 2 = q * q0)
    (h1 : (q : ℤ) ∣ x + y * z) (h2 : (q0 : ℤ) ∣ x + y * z0) :
    I * P = span {(x : 𝓞 K) + (y : 𝓞 K) * D.θ} := by
  have hcop : I ⊔ P = ⊤ := by
    obtain ⟨u, v, huv⟩ : IsCoprime (q : ℤ) (q0 : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hq hq0).mpr hqq)
    rw [eq_top_iff_one]
    have h1' : (1 : 𝓞 K) = ((u : ℤ) : 𝓞 K) * ((q : ℤ) : 𝓞 K) + ((v : ℤ) : 𝓞 K) * ((q0 : ℤ) : 𝓞 K) := by
      have := congrArg (Int.cast (R := 𝓞 K)) huv
      push_cast at this ⊢
      exact this.symm
    rw [h1']
    refine Submodule.add_mem_sup (I.mul_mem_left _ ?_) (P.mul_mem_left _ ?_)
    · simpa using natCast_mem_of_absNorm_eq' hI
    · simpa using natCast_mem_of_absNorm_eq' hP
  symm
  apply eq_of_le_of_absNorm_eq
  · rw [mul_eq_inf_of_coprime hcop, span_singleton_le_iff_mem]
    exact ⟨add_mul_mem_of_dvd D hI hz h1, add_mul_mem_of_dvd D hP hz0 h2⟩
  · rw [map_mul, hI, hP, absNorm_span_singleton, D.norm_eq, hQ]
    norm_cast
  · rw [map_mul, hI, hP]; exact mul_ne_zero hq.ne_zero hq0.ne_zero

end QuadInt

/-! ### Class number two -/

open CN1.Finite CN1.Foundations in
/-- **Class number two from a bridge certificate.** For `K` of degree two containing `√-m`, `m` squarefree: if the
bridge certificate holds with `4·dOf m < 9·B²` (so the Minkowski bound is below `B`) and `Q` does not represent `q₀`,
then `classNumber K = 2`. -/
theorem classNumber_eq_two_of_bridge (hK : finrank ℚ K = 2) {m : ℕ} (hm : Squarefree m)
    (hsq : ∃ α : K, α ^ 2 = -(m : K)) {B q0 z0 : ℕ} {W : List BWit} (hB : 4 * dOf m < 9 * B ^ 2)
    (hcert : BridgeCert (tOf m) (cOf m) B q0 z0 W = true) (hnr : NotRep (tOf m) (cOf m) q0) :
    classNumber K = 2 := by
  classical
  obtain ⟨α, hα⟩ := hsq
  set D := quadIntOfFoundations hK hm hα
  have htc := tOf_mul_lt_four_mul_cOf hm.ne_zero
  have hdisc : |discr K| ≤ (dOf m : ℤ) := by rw [discr_eq hα hK hm, abs_neg, Nat.abs_cast, disc_eq_dOf]
  simp only [BridgeCert, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hcert
  obtain ⟨⟨⟨⟨hq0, hz0lt⟩, hroot0⟩, huniq⟩, hall⟩ := hcert
  have hq0p : q0.Prime := primeB_sound hq0
  -- the prime `P₀` of norm `q₀`, with residue `z₀`
  obtain ⟨P0, hP0⟩ := exists_absNorm_eq_of_root D hq0p z0 (rootB_iff.mp hroot0)
  have hres : ∀ {J : Ideal (𝓞 K)}, absNorm J = q0 → D.θ - ((z0 : ℤ) : 𝓞 K) ∈ J := by
    intro J hJ
    obtain ⟨z, hzlt, hzr, hzJ⟩ := exists_residue D hq0p hJ
    have : z = z0 := by
      rcases huniq z hzlt with h | h
      · rw [hzr] at h; exact absurd h (by decide)
      · exact h
    rwa [this] at hzJ
  have hP0res := hres hP0
  let P : (Ideal (𝓞 K))⁰ := ⟨P0, mem_nonZeroDivisors_of_absNorm_eq hq0p hP0⟩
  -- `g = [P₀]` has `g² = 1`: the ideal `J₀` with `P₀·J₀ = (q₀)` is `P₀`
  obtain ⟨J0, hJ0, hPJ⟩ := exists_mul_eq_span_of_absNorm_eq D hq0p hP0
  have hJP : J0 = P0 := eq_of_sub_mem D htc hq0p hJ0 hP0 (hres hJ0) hP0res
  have hginv : ClassGroup.mk0 P = (ClassGroup.mk0 P)⁻¹ :=
    ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨q0, by exact_mod_cast hq0p.ne_zero, by
      show P0 * P0 = _; rw [hJP] at hPJ; exact hPJ⟩
  have hg2 : ClassGroup.mk0 P * ClassGroup.mk0 P = 1 := by
    rw [mul_eq_one_iff_eq_inv]; exact hginv
  have hg1 : ClassGroup.mk0 P ≠ 1 := mk0_ne_one D htc.le P (by show NotRep _ _ (absNorm P0); rw [hP0]; exact hnr)
  -- the submonoid `{1, g}`
  let S : Submonoid (ClassGroup (𝓞 K)) :=
    { carrier := {x | x = 1 ∨ x = ClassGroup.mk0 P}
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl)
        · exact Or.inl (one_mul 1)
        · exact Or.inr (one_mul _)
        · exact Or.inr (mul_one _)
        · exact Or.inl hg2
      one_mem' := Or.inl rfl }
  have hS : ∀ C, C ∈ S := mem_of_forall_prime_le_minkowski S (fun I hIp hle => by
    have hI0 : (I : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
    haveI hmax : (I : Ideal (𝓞 K)).IsMaximal := hIp.isMaximal hI0
    obtain ⟨q, hq, -, hcase⟩ := absNorm_maximal_cases hK (I : Ideal (𝓞 K))
    rcases hcase with hN | ⟨-, hspan⟩
    · have hbound := le_two_thirds_sqrt_of_le_minkowski hK hdisc hle
      rw [hN] at hbound
      have hqB : q < B := nat_lt_of_le_two_thirds_sqrt hbound hB
      obtain ⟨z, hzlt, hzr, hzI⟩ := exists_residue D hq hN
      rcases hall q hqB with h | h
      · exact absurd (primeB_of_prime hq) (by rw [h]; decide)
      rcases h z hzlt with (h | h) | h
      · rw [hzr] at h; exact absurd h (by decide)
      · -- `q = q₀`: then `z = z₀` and `I = P₀`
        subst h
        have hz : z = z0 := by
          rcases huniq z hzlt with h' | h'
          · rw [hzr] at h'; exact absurd h' (by decide)
          · exact h'
        subst hz
        have : (I : Ideal (𝓞 K)) = P0 := eq_of_sub_mem D htc hq hN hP0 hzI hP0res
        right
        congr 1
        exact Subtype.ext this
      · obtain ⟨w, -, hw⟩ := List.any_eq_true.mp h
        simp only [witOK, Bool.and_eq_true, beq_iff_eq] at hw
        obtain ⟨⟨⟨hwq, hwz⟩, hwd⟩, hwg⟩ := hw
        have h1 : (q : ℤ) ∣ w.x + w.y * z := Int.dvd_of_emod_eq_zero hwd
        by_cases hg : w.g = true
        swap
        · -- principal
          rw [Bool.not_eq_true] at hg
          rw [hg] at hwg
          simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq, formZ] at hwg
          left
          rw [ClassGroup.mk0_eq_one_iff (I.2)]
          rw [← span_eq_of_witness D hq hN hzI hwg h1]
          exact ⟨⟨_, rfl⟩⟩
        · rw [hg] at hwg
          simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, formZ] at hwg
          obtain ⟨⟨hQ, hd0⟩, hqq⟩ := hwg
          have h2 : (q0 : ℤ) ∣ w.x + w.y * z0 := Int.dvd_of_emod_eq_zero hd0
          have hmul := mul_eq_span_of_witness D hq hq0p hqq hN hP0 hzI hP0res (by rw [hQ]) h1 h2
          right
          have hinv : ClassGroup.mk0 I = (ClassGroup.mk0 P)⁻¹ :=
            ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨_, by
              intro h0
              rw [h0, span_singleton_eq_bot.mpr rfl] at hmul
              have := congrArg absNorm hmul
              rw [map_mul, hN, hP0, absNorm_bot] at this
              exact mul_ne_zero hq.ne_zero hq0p.ne_zero this, hmul⟩
          rw [hinv, ← hginv]
    · left
      rw [ClassGroup.mk0_eq_one_iff (I.2), hspan]
      exact ⟨⟨_, rfl⟩⟩)
  have huniv : (Finset.univ : Finset (ClassGroup (𝓞 K))) = {1, ClassGroup.mk0 P} := by
    ext C
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hS C
  unfold classNumber
  rw [← Finset.card_univ, huniv, Finset.card_pair hg1.symm]

end HCN.Finite
