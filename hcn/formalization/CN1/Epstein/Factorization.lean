import CN1.Foundations.Splitting
import CN1.Foundations.Ramified
import CN1.Epstein.IdealCount
import CN1.Epstein.PrimePower

/-!
# `ζ_K(s) = ζ(s) · L(s, χ_{-d})` on `Re s > 1` (step 2 of the argument)

Pinned environment: Lean v4.34.1, Mathlib d13f23b.

For the statement's `K` (`finrank 2`, `α² = -m`, `m` squarefree), the ideal-counting function
`a_K = idealCount K` (multiplicative, `IdealCount.lean`) agrees at prime powers with the Dirichlet
convolution `ζ ⋆ χ` of `1` with `χ = kroneckerChar m` (Mathlib's `DirichletCharacter.zetaMul`):
`a_K(p^k) = Σ_{j ≤ k} χ(p)^j`, i.e. `k + 1` if `p` splits (`χ(p) = 1`), `[k even]` if `p` is inert
(`χ(p) = -1`), `1` if `p` ramifies (`χ(p) = 0`). The splitting data come from
`CN1.Foundations.Splitting` / `CN1.Foundations.Ramified`, the counts from `PrimePower.lean`. Then
`a_K = ζ ⋆ χ` by multiplicativity, and `LSeries_mul'`, `LSeries_zeta_eq_riemannZeta` and
`LFunction_eq_LSeries` give the factorisation of `NumberField.dedekindZeta K`.
-/

set_option autoImplicit false

namespace CN1.Epstein

open NumberField Ideal CN1.Foundations

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
  (hK : Module.finrank ℚ K = 2) (hm : Squarefree m)

/-- `d = disc m ≠ 0` for `m ≠ 0`. -/
theorem disc_ne_zero {m : ℕ} (hm0 : m ≠ 0) : disc m ≠ 0 := by
  unfold disc; split_ifs <;> omega

include hα hK hm in
/-- **The splitting law in coefficient form.** For every prime `p` and `k ≥ 0`,
`#{I : N(I) = p^k} = Σ_{j ≤ k} χ_{-d}(p)^j`. -/
theorem card_absNorm_eq_prime_pow (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    (Nat.card {I : Ideal (𝓞 K) // absNorm I = p ^ k} : ℂ) =
      ∑ i ∈ Finset.range (k + 1), kroneckerChar m (p : ZMod (disc m)) ^ i := by
  by_cases hpd : p ∣ disc m
  · -- ramified: one prime of norm `p`, `χ(p) = 0`
    rw [kroneckerChar_eq_zero_of_dvd_disc p hpd]
    obtain ⟨h1, hdeg⟩ := ramified_of_dvd_disc hα hK hm p hpd
    rw [card_absNorm_eq_pow_of_ncard_eq_one p h1 one_pos (fun P hP => (hdeg P hP).1) k,
      if_pos (one_dvd k), Finset.sum_range_succ']
    simp
  · rcases kroneckerChar_eq_one_or_neg_one p hpd with h | h
    · -- split: two primes of norm `p`, `χ(p) = 1`
      rw [h]
      obtain ⟨h2, hdeg⟩ := ncard_primesOver_eq_two_of_kroneckerChar_eq_one hα hK hm p hpd h
      rw [card_absNorm_eq_pow_of_ncard_eq_two p h2 hdeg k]
      simp
    · -- inert: one prime of norm `p²`, `χ(p) = -1`
      rw [h]
      obtain ⟨h1, hdeg⟩ := ncard_primesOver_eq_one_of_kroneckerChar_eq_neg_one hα hK hm p hpd h
      rw [card_absNorm_eq_pow_of_ncard_eq_one p h1 two_pos hdeg k, neg_one_geom_sum]
      by_cases hk : 2 ∣ k
      · have : Even (k + 1) ↔ False := by
          rw [Nat.even_add_one, even_iff_two_dvd]; exact ⟨fun h' => h' hk, False.elim⟩
        simp [hk, this]
      · have : Even (k + 1) := by
          rw [Nat.even_add_one, even_iff_two_dvd]; exact hk
        simp [hk, this]

/-- `(ζ ⋆ χ)(p^k) = Σ_{j ≤ k} χ(p)^j` for any Dirichlet character `χ` (Mathlib's `zetaMul`). -/
theorem zetaMul_apply_prime_pow {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime)
    (k : ℕ) : χ.zetaMul (p ^ k) = ∑ i ∈ Finset.range (k + 1), χ (p : ZMod N) ^ i := by
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← DirichletCharacter.apply_eq_toArithmeticFunction_apply _ (pow_ne_zero _ hp.ne_zero),
    Nat.cast_pow, map_pow]

include hα hK hm in
/-- **`a_K = ζ ⋆ χ_{-d}`** as arithmetic functions. -/
theorem idealCount_eq_zetaMul : idealCount K = (kroneckerChar m).zetaMul := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_idealCount K)
    _ (DirichletCharacter.isMultiplicative_zetaMul _)]
  intro p i hp
  haveI := Fact.mk hp
  rw [idealCount_apply K (pow_ne_zero _ hp.ne_zero), card_absNorm_eq_prime_pow hα hK hm p i,
    zetaMul_apply_prime_pow _ hp]

include hα hK hm in
/-- **`ζ_K(s) = ζ(s) · L(s, χ_{-d})` for `Re s > 1`** (step 2 of the argument). -/
theorem dedekindZeta_eq_riemannZeta_mul_LFunction [NeZero (disc m)] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction (kroneckerChar m) s := by
  have hζ : LSeriesSummable
      (⇑((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hχ : LSeriesSummable (⇑(toArithmeticFunction (fun n : ℕ => kroneckerChar m n))) s := by
    refine (LSeriesSummable_congr s (fun hn => ?_)).mp
      (DirichletCharacter.LSeriesSummable_of_one_lt_re (kroneckerChar m) hs)
    exact DirichletCharacter.apply_eq_toArithmeticFunction_apply _ hn
  rw [dedekindZeta_eq_LSeries_idealCount, idealCount_eq_zetaMul hα hK hm,
    DirichletCharacter.zetaMul, ArithmeticFunction.LSeries_mul' hζ hχ,
    DirichletCharacter.LFunction_eq_LSeries _ hs]
  congr 1
  · exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  · exact LSeries_congr (fun hn => (DirichletCharacter.apply_eq_toArithmeticFunction_apply _ hn).symm) s

end CN1.Epstein
