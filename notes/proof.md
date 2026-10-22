# The class number one theorem without Heegner: a human-readable account of a kernel-checked proof

This note walks through a proof, written in Lean 4 and checked by two independent kernels, of the classical theorem that the imaginary quadratic fields of class number one are exactly the nine fields ℚ(√−m) with m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}. The proof does not go through Heegner's modular-function argument, nor through Baker's or Stark's linear forms in logarithms, nor through Goldfeld–Gross–Zagier. Instead it uses the recent theorem (openai/math, family 003) that Dirichlet L-functions have no zeros in the half-plane Re s > 7/8, combined with the Chowla–Selberg formula and a short finite computation. The route was proposed in the comments of Terence Tao's blog post of 20 October 2026, which asked whether the new Siegel-zero-free arguments could be turned into an explicit bound on a hypothetical tenth class-number-one discriminant. Our answer is that they can, that the bound is d ≤ 652, and that the whole argument, from the definition of the class number in Mathlib to the last witness prime, goes through the Lean kernel.

The note is written for a number theorist who wants to understand what was proved and how, in about an hour, and who may then want to look at the Lean code. Every step of the human argument is paired with the name of the Lean lemma that carries it, with a file and line reference into the development (paths are relative to this repository, so `formalization/CN1/...`). There is no opaque monolith: the proof of the main theorem is a dozen lines that call the named pieces, and each piece is a theorem a reader can inspect on its own. The mathematical claims are those of the Lean development; the history, the attributions and the account of how the proof was checked are ours, and we say how each was obtained.

---

## 1. The theorem, as the kernel sees it

The statement that Comparator checks is this one (`CN1.classNumber_eq_one_iff`, formalization/CN1Challenges/ClassNumberOne.lean:32, where it carries a `sorry`; the proof is in formalization/CN1/Main.lean:36):

```lean
theorem classNumber_eq_one_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)
```

In words: let K be a number field of degree two over ℚ, let m be a squarefree natural number, and suppose K contains a square root of −m. Then K has class number one if and only if m is one of the nine listed values.

A few remarks on why this phrasing pins down K = ℚ(√−m) and nothing else. In Mathlib, `Squarefree 0` is false (0 is divisible by every square), so the hypothesis `Squarefree m` forces m ≥ 1. For m ≥ 1 the rational number −m is negative, hence not a square in ℚ, so the element α with α² = −m is not rational. Both facts are recorded as a small lemma next to the candidate statements (`CN1.Candidates.squarefree_ne_zero_and_not_isSquare_neg`, formalization/CN1Challenges/Candidates.lean:46). Since α is irrational and K has degree two, K = ℚ(α) ≅ ℚ[X]/(X² + m) ≅ ℚ(√−m). The statement is therefore about every model of ℚ(√−m), in any universe, not about one particular construction; this is why it is stated for an abstract K with hypotheses rather than for a concrete `AdjoinRoot`.

The squarefree hypothesis is load-bearing. Without it, m = 4 with K = ℚ(i) satisfies α² = −4 (take α = 2i), K has class number one, and 4 is not in the list, so the statement would be false. One of the negative controls in section 4 is exactly this tampered statement, and Comparator rejects it.

The radicand m and the discriminant d. Throughout, we write d = |disc K|. The relation is d = m when m ≡ 3 (mod 4) and d = 4m otherwise, so the nine fields have d ∈ {4, 8, 3, 7, 11, 19, 43, 67, 163}. The statement is in terms of m because that is what makes it a one-screen statement over Mathlib's vocabulary; the analytic argument is in terms of d because that is what Chowla–Selberg wants. The function `CN1.Foundations.disc` (formalization/CN1/Foundations/Basic.lean:34) is the translation, and the Lean proof shows it really is |disc K| (`CN1.Foundations.discr_eq`, formalization/CN1/Foundations/Discr.lean:56).

What a reader has to trust. The trust base is deliberately small and we want to state it precisely.

- The statement above, including the Mathlib definitions it uses: `NumberField`, `NumberField.classNumber` (the cardinality of the class group of the ring of integers), `Module.finrank`, and `Squarefree`. Everything else in the statement is Lean's own arithmetic and set notation.
- The Lean 4 kernel (v4.34.1) and, independently, the nanoda kernel, a from-scratch reimplementation of Lean's type checker. Both replayed the exported proof.
- The three standard axioms of Lean's classical mathematics: `propext`, `Quot.sound`, and `Classical.choice`. Nothing else is permitted; in particular no `sorry`, no `native_decide`, and no additional axiom.

The theorem of openai/math that we use is not on this list. Its Lean proof is inside the dependency closure that both kernels checked. That the accompanying manuscript is unrefereed bears on how well humans understand the proof, not on whether the kernel accepted it.

## 2. The route, in one paragraph

Suppose K = ℚ(√−m) has class number one and m is not 1 or 3. Then every ideal of its ring of integers is principal and the only units are ±1, so counting ideals by norm is the same as counting lattice points by the value of the principal binary quadratic form Q, and the Dedekind zeta function of K is half an Epstein zeta function: ζ_K(s) = ½ Σ′ Q(x, y)^{−s}. On the other hand ζ_K(s) = ζ(s) L(s, χ) where χ is the Kronecker character of K. The Chowla–Selberg formula continues the Epstein sum past Re s = 1 as an explicit main term plus an exponentially small remainder, and at s = 7/8 the main term is ζ(7/4) + C d^{−3/8} ζ(3/4) with C ≈ 6.4847 and ζ(3/4) < 0, which is an increasing function of d that crosses zero near d ≈ 654. But ζ(7/8) < 0, and L(7/8, χ) ≥ 0 by the zero-free region Re s > 7/8 together with positivity for σ > 1, so ζ(7/8) L(7/8, χ) ≤ 0, which forces d ≤ 652. For d ≤ 652 the question is finite: for each of the 190 non-Heegner discriminants in range there is a small split prime that cannot be the norm of a principal ideal, so the class number is not one; and the nine Heegner fields have class number one by the Minkowski bound. The proof uses no Heegner, Baker, Stark or Gross–Zagier; its one deep input is the 7/8 zero-free region for Dirichlet L-functions from openai/math (family 003, unrefereed, but with a Lean proof that is inside our checked closure).

## 3. The steps, one Lean lemma at a time

### 3a. Foundations: the ring of integers, the norm form, the character, the splitting law

Fix K, m, α as in the statement, with hα : α² = −m, hK : [K : ℚ] = 2, hm : m squarefree. Set

- ω = (1 + α)/2 if m ≡ 3 (mod 4), and ω = α otherwise (`CN1.Foundations.omega`, formalization/CN1/Foundations/Basic.lean:45);
- Q(x, y) = x² + xy + ((m + 1)/4) y² if m ≡ 3 (mod 4), and Q(x, y) = x² + m y² otherwise (`CN1.Foundations.principalForm`, formalization/CN1/Foundations/Basic.lean:38);
- d = m if m ≡ 3 (mod 4), and d = 4m otherwise (`CN1.Foundations.disc`, formalization/CN1/Foundations/Basic.lean:34).

The first structural fact is that the ring of integers is ℤ[ω]. The proof is the classical trace-and-norm argument: an integral element x = a + bα (a, b ∈ ℚ) has integral trace 2a and integral norm a² + m b², so m(2b)² ∈ ℤ, and because m is squarefree this forces 2b ∈ ℤ; a check mod 4 then sorts out the parities in the three residue classes of m. This is where `Squarefree m` is used. In Lean: `CN1.Foundations.exists_int_add_int_mul_omega_of_isIntegral` (formalization/CN1/Foundations/Basic.lean:221) shows every integral element is u + vω with u, v ∈ ℤ, and `CN1.Foundations.intBasis` (formalization/CN1/Foundations/Basic.lean:325) packages {1, ω} as a ℤ-basis of 𝓞_K. The element ω itself lives in 𝓞_K as `CN1.Foundations.omegaInt` (formalization/CN1/Foundations/Basic.lean:302).

The norm form. For integers x, y, the norm of x + yω is Q(x, y): `CN1.Foundations.norm_int_eq_principalForm` (formalization/CN1/Foundations/Basic.lean:388). Q is positive semidefinite (`principalForm_nonneg`, formalization/CN1/Foundations/Basic.lean:395), and Q(x, y) = 1 forces y = 0 and x = ±1 once m ∉ {1, 3} (`CN1.Foundations.principalForm_eq_one`, formalization/CN1/Foundations/Basic.lean:406). The reason for the exclusion is visible in the inequality 4Q = (2x + y)² + d y² ≥ d for y ≠ 0 (or 4Q = 4x² + 4m y² ≥ 4m): with d ≥ 7 or m ≥ 2 the form cannot take the value 1 off the x-axis. For m = 1 and m = 3 it can, because ℚ(i) and ℚ(√−3) have 4 and 6 units.

The units. A unit has norm ±1, and the norm is a positive definite form, so the norm is 1 and the previous lemma gives ε = ±1: `CN1.Foundations.coe_unit_eq_one_or_neg_one` (formalization/CN1/Foundations/Basic.lean:444), with hypotheses m ≠ 1 and m ≠ 3.

The character. The Kronecker character χ = χ_{−d} is built as a Mathlib `DirichletCharacter ℂ d`, that is, a multiplicative character on ZMod d with values in ℂ, of level exactly d. It is built case by case from the Jacobi symbol and the characters χ₄, χ₈, χ₈′ of Mathlib, and lifted to level d with `changeLevel`: for m ≡ 3 (mod 4) it is the Jacobi symbol (· | m); for m ≡ 1 (mod 4) it is χ₄ · (· | m) at level 4m; for m ≡ 2 (mod 4) it is χ₈′ · (· | m/2) or χ₈ · (· | m/2) according to m/2 mod 4, at level 4m (`CN1.Foundations.kroneckerChar`, formalization/CN1/Foundations/Character.lean:151). Its basic properties: it is quadratic, meaning its values lie in {−1, 0, 1} (`kroneckerChar_isQuadratic`, formalization/CN1/Foundations/Character.lean:194); it is odd, χ(−1) = −1 (`kroneckerChar_neg_one`, formalization/CN1/Foundations/Character.lean:218); and consequently it is not the trivial character (`kroneckerChar_ne_one`, formalization/CN1/Foundations/Character.lean:240). At an odd prime p not dividing d its value is the Legendre symbol (−m | p), by quadratic reciprocity for the Jacobi symbol in each residue class (`kroneckerChar_apply_prime_of_ne_two`, formalization/CN1/Foundations/Character.lean:293), and at p = 2 with m ≡ 3 (mod 4) it is χ₈(m) (`kroneckerChar_apply_two`, formalization/CN1/Foundations/Character.lean:312). Because the level is exactly d, χ(p) = 0 if and only if p | d (`kroneckerChar_eq_zero_of_dvd_disc`, formalization/CN1/Foundations/Ramified.lean:28).

The splitting law. The minimal polynomial of ω over ℤ is X² + bX + c with (b, c) = (−1, (m + 1)/4) for m ≡ 3 (mod 4) and (0, m) otherwise (`CN1.Foundations.bInt`, `cInt`, formalization/CN1/Foundations/Splitting.lean:40 and :43; `minpoly_int_omegaInt`, formalization/CN1/Foundations/Splitting.lean:121), and its discriminant is b² − 4c = −d (`bInt_sq_sub_four_mul_cInt`, formalization/CN1/Foundations/Splitting.lean:46). Since 𝓞_K = ℤ[ω], the conductor is trivial and Mathlib's Kummer–Dedekind theorem for number fields (`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`) applies at every prime: the primes of 𝓞_K above p correspond to the monic irreducible factors of X² + bX + c mod p, with inertia degree the degree of the factor (`exponent_omegaInt_eq_one`, formalization/CN1/Foundations/Splitting.lean:73). For p ∤ d the quadratic has a root mod p exactly when χ(p) = 1 (`kroneckerChar_eq_one_iff_exists_root`, formalization/CN1/Foundations/Splitting.lean:291), and the root criterion gives the full dictionary:

- χ(p) = 1: two primes above p, each of inertia degree 1 (`ncard_primesOver_eq_two_of_kroneckerChar_eq_one`, formalization/CN1/Foundations/Splitting.lean:329); in particular there is a prime ideal of norm p (`exists_prime_absNorm_eq_of_kroneckerChar_eq_one`, formalization/CN1/Foundations/Splitting.lean:392);
- χ(p) = −1: one prime above p, of inertia degree 2 (`ncard_primesOver_eq_one_of_kroneckerChar_eq_neg_one`, formalization/CN1/Foundations/Splitting.lean:351);
- p | d (so χ(p) = 0): X² + bX + c ≡ (X − r)² mod p, one prime above p, inertia degree 1 and ramification index 2 (`ramified_of_dvd_disc`, formalization/CN1/Foundations/Ramified.lean:101).

Finally the discriminant of K is −d (`CN1.Foundations.discr_eq`, formalization/CN1/Foundations/Discr.lean:56), computed from the ℤ-basis {1, ω} via Mathlib's `NumberField.discr_eq_discr`.

All of this imports only Mathlib. None of it uses the 7/8 theorem.

### 3b. Class number one implies ζ_K = ½ Σ′ Q^{−s}

Assume now that the class number is one and m ∉ {1, 3}. Mathlib's `NumberField.classNumber_eq_one_iff` says class number one is the same as 𝓞_K being a principal ideal ring.

Mathlib defines the Dedekind zeta function as the L-series of the ideal-counting function, ζ_K(s) = Σ_n a_K(n) n^{−s} with a_K(n) = #{I ⊆ 𝓞_K : N(I) = n} (`NumberField.dedekindZeta`). We record that function as an `ArithmeticFunction` (`CN1.Epstein.idealCount`, formalization/CN1/Epstein/IdealCount.lean:183; `dedekindZeta_eq_LSeries_idealCount`, formalization/CN1/Epstein/IdealCount.lean:192).

The lattice side. The map (x, y) ↦ x + yω is a bijection ℤ² → 𝓞_K (`CN1.Epstein.intPairEquiv`, formalization/CN1/Epstein/Lattice.lean:114) carrying Q to the norm. For Re s > 1 the sum Σ_{(x,y)} Q(x, y)^{−s} converges absolutely, because Q(x, y) ≥ ½(x² + y²) (`summable_principalForm_cpow`, formalization/CN1/Epstein/Lattice.lean:95; Mathlib's Eisenstein-series summability does the work). The (0, 0) term is 0^{−s} = 0 in Mathlib's complex power, so the sum over ℤ² is already the primed sum.

Regroup by norm. For each n ≥ 1, the nonzero elements of norm n are in bijection with (units) × (ideals of norm n), via (u, I) ↦ u · generator(I); this uses that every ideal is principal and that two generators of the same ideal differ by a unit (`CN1.Epstein.unitsProdEquiv`, formalization/CN1/Epstein/Lattice.lean:195). There are exactly two units (`CN1.Epstein.card_units_eq_two`, formalization/CN1/Epstein/Lattice.lean:219, from 3a), so #{z ≠ 0 : |N z| = n} = 2 a_K(n) (`card_nonzero_normNat_eq`, formalization/CN1/Epstein/Lattice.lean:234). Summing fibrewise along z ↦ |N z| (Mathlib's `HasSum.tsum_fiberwise`) gives

  Σ′_{(x,y)} Q(x, y)^{−s} = 2 Σ_n a_K(n) n^{−s} = 2 ζ_K(s)  for Re s > 1

(`CN1.Epstein.latticeSum_eq_two_mul_LSeries`, formalization/CN1/Epstein/Lattice.lean:245), and hence

  ζ_K(s) = ½ Σ′_{(x,y)} Q(x, y)^{−s}

(`CN1.Epstein.dedekindZeta_eq_half_latticeSum`, formalization/CN1/Epstein/Lattice.lean:302; hypotheses hm1 : m ≠ 1, hm3 : m ≠ 3, h1 : classNumber K = 1, hs : 1 < Re s).

The factor ½ is 1/w with w the number of units; this is the one place where m ∉ {1, 3} enters the analytic half of the argument. Since 1 and 3 are among the nine, we only ever need this step for m outside the nine, so the exclusion costs nothing.

### 3c. ζ_K = ζ · L(·, χ)

This step holds for every squarefree m, with no class number hypothesis. The strategy is coefficientwise: both ζ_K and ζ · L(·, χ) are Dirichlet series with multiplicative coefficients, so it is enough to compare them at prime powers.

Multiplicativity of a_K. For coprime a, b and an ideal I of norm ab, the map I ↦ (I + (a), I + (b)) is a bijection onto pairs of ideals of norms a and b, with inverse (J, J′) ↦ JJ′. The key observations are that ab = N(I) ∈ I and (a) + (b) = (1), so (I + (a))(I + (b)) = I, and that N(I + (a)) divides both ab and a², hence a, while the two norms multiply to ab (`CN1.Epstein.card_absNorm_eq_mul`, formalization/CN1/Epstein/IdealCount.lean:169; `isMultiplicative_idealCount`, formalization/CN1/Epstein/IdealCount.lean:198). This is about 120 lines over Mathlib and avoids any dependence on Euler products.

Ideals of norm p^k. Every prime factor of such an ideal lies above p, so by unique factorisation of ideals the ideal is P^k (one prime P of norm p), P^{k/2} when k is even and nothing when k is odd (one prime of norm p²), or P₁^i P₂^{k−i} for 0 ≤ i ≤ k (two primes of norm p). The counts are 1, [k even], and k + 1 respectively (`CN1.Epstein.card_absNorm_eq_pow_of_ncard_eq_one`, formalization/CN1/Epstein/PrimePower.lean:101; `card_absNorm_eq_pow_of_ncard_eq_two`, formalization/CN1/Epstein/PrimePower.lean:173). Matching this against the splitting law of 3a gives, in all three cases,

  a_K(p^k) = Σ_{i=0}^{k} χ(p)^i

(`CN1.Epstein.card_absNorm_eq_prime_pow`, formalization/CN1/Epstein/Factorization.lean:37). The right side is the coefficient of ζ · L(·, χ) at p^k, since Mathlib's `DirichletCharacter.zetaMul χ` is the Dirichlet convolution 1 ⋆ χ (`zetaMul_apply_prime_pow`, formalization/CN1/Epstein/Factorization.lean:66). Two multiplicative functions agreeing on prime powers are equal (`idealCount_eq_zetaMul`, formalization/CN1/Epstein/Factorization.lean:76), and the L-series of a convolution is the product of the L-series on the common half-plane of absolute convergence, so

  ζ_K(s) = ζ(s) · L(s, χ)  for Re s > 1

(`CN1.Epstein.dedekindZeta_eq_riemannZeta_mul_LFunction`, formalization/CN1/Epstein/Factorization.lean:86). Here `riemannZeta` and `DirichletCharacter.LFunction` are Mathlib's analytically continued functions; on Re s > 1 they agree with the Dirichlet series.

Putting 3b and 3c together: for class number one and m ∉ {1, 3},

  ζ(s) · L(s, χ_{−d}) = ½ Σ′_{(x,y)} Q(x, y)^{−s}  for Re s > 1

(`CN1.Epstein.epstein_identity`, formalization/CN1/Epstein/Epstein.lean:33). A bridge lemma rewrites the right side in the notation of the Chowla–Selberg module, whose principal form is written in terms of d rather than m (`principalForm_cast_eq_Q`, formalization/CN1/Epstein/Bridge.lean:35; `CN1.Epstein.epstein_identity_Z`, formalization/CN1/Epstein/Bridge.lean:66). This is the identity that the assembly in 3i feeds into the analytic machinery.

### 3d. Chowla–Selberg with an explicit remainder, continued to s = 7/8

Now we leave number fields behind. Fix an integer d ≥ 3 with d ≡ 0 or 3 (mod 4) (`CN1.CS.IsDisc`, formalization/CN1/ChowlaSelberg/Form.lean:21), and write b = d mod 2, c = (d + b)/4, Q(x, y) = x² + bxy + cy² (`CN1.CS.Q`, formalization/CN1/ChowlaSelberg/Form.lean:30), and

  Z_d(s) = Σ_{(x,y) ∈ ℤ²} Q(x, y)^{−s}

(`CN1.CS.Z`, formalization/CN1/ChowlaSelberg/Form.lean:34; again the origin contributes 0). Completing the square, Q(x, y) = (x + by/2)² + (d/4) y² (`Q_eq`, formalization/CN1/ChowlaSelberg/Form.lean:49), and Q ≥ ½(x² + y²) (`Q_ge_half`, formalization/CN1/ChowlaSelberg/Form.lean:56), so Z_d converges absolutely for Re s > 1 (`summable_Q_cpow`, formalization/CN1/ChowlaSelberg/Form.lean:132).

The classical formula. For Re s > 1,

  ½ Z_d(s) = ζ(2s) + 2^{2s−1} √π · Γ(s − ½)/Γ(s) · d^{½−s} · ζ(2s − 1) + E_d(s),

where E_d(s) is the Bessel remainder. In the usual presentation one writes E_d(s) as

  2^{s+3/2} π^s / (Γ(s) d^{s/2−1/4}) · Σ_{n≥1} n^{s−1/2} σ_{1−2s}(n) cos(πbn) K_{s−1/2}(πn√d),

with σ the divisor function and K the modified Bessel function. (The prefactor is 2^{s+3/2}, not 2^{s+1/2}; an earlier script of ours had the latter, which is invisible numerically for d ≥ 67 where the whole term is around 10^{−11}, and was caught by cross-checking against direct lattice sums at s = 2 and small d. The threshold below is unaffected.) The Lean development never names a Bessel function. It defines E_d directly as a double series of Mellin-type integrals, which is the form in which the formula is actually proved, and the Bessel series above is a closed-form rewriting of it that we checked numerically but do not use.

How it is proved. The idea is Poisson summation in x for each fixed y, after writing Q^{−s} as a Gamma integral.

1. The Gamma integral. For a, b ≥ 0 with a > 0, define

   I(s; a, b) = ∫₀^∞ t^{s−3/2} e^{−at − b/t} dt,

   realised as the Mellin transform of t ↦ e^{−at−b/t} at s − ½ (`CN1.CS.I`, formalization/CN1/ChowlaSelberg/GammaIntegral.lean:28). For b = 0 it is the Gamma integral (1/a)^{s−½} Γ(s − ½) (`I_zero`, formalization/CN1/ChowlaSelberg/GammaIntegral.lean:117). The one inequality that controls everything is, for Re s > ½,

   ‖I(s; a, b)‖ ≤ e^{−√(ab)} · (2/a)^{Re s − ½} · Γ(Re s − ½)

   (`CN1.CS.norm_I_le`, formalization/CN1/ChowlaSelberg/GammaIntegral.lean:157). Its proof is AM–GM on the exponent: at + b/t ≥ 2√(ab), so e^{−at−b/t} ≤ e^{−√(ab)} e^{−at/2}, and the remaining integral is a Gamma integral. This is the whole of the "K-Bessel inequality" and the "tail bound" that a classical treatment would quote; here they are a few lines.

2. Poisson in x with a shift. Mathlib's `Complex.tsum_exp_neg_quadratic` gives the Jacobi theta identity with a real shift,

   Σ_n e^{−πt(n+α)²} = t^{−½} Σ_k e^{−πk²/t} e^{2πikα}

   (`CN1.CS.theta_shift`, formalization/CN1/ChowlaSelberg/PoissonSlice.lean:48). With α = by/2 the phase e^{2πikα} is (−1)^{kby}, a sign (`CN1.CS.sgn`, formalization/CN1/ChowlaSelberg/PoissonSlice.lean:83).

3. The slice lemma. For y ≠ 0 and Re s > 1,

   Σ_x Q(x, y)^{−s} = (π^s/Γ(s)) Σ_k (−1)^{kby} I(s; πdy²/4, πk²)

   (`CN1.CS.slice`, formalization/CN1/ChowlaSelberg/PoissonSlice.lean:190; the two parameters are `ay d y = πdy²/4` and `bk k = πk²`, formalization/CN1/ChowlaSelberg/PoissonSlice.lean:98 and :101). This is the hardest lemma of the analytic part: it writes each Q^{−s} as a Gamma integral, exchanges sum and integral, applies the theta identity, and exchanges back; both exchanges go through Mathlib's `integral_tsum_of_summable_integral_norm`, with the summability supplied by step 1.

4. Assembly. The y = 0 slice is Σ_{x≠0} (x²)^{−s} = 2ζ(2s) (`CN1.CS.tsum_int_sq_cpow`, formalization/CN1/ChowlaSelberg/MainTerm.lean:43). In each y ≠ 0 slice the k = 0 term is the Gamma integral (4/(πdy²))^{s−½} Γ(s − ½), and summing it over y ≠ 0 produces 2ζ(2s − 1) times (4/(πd))^{s−½} Γ(s − ½). What is left is the remainder:

   E_d(s) = π^s/(2Γ(s)) · Σ_{y≠0} Σ_{k≠0} (−1)^{kby} I(s; πdy²/4, πk²)

   (`CN1.CS.Rterm`, `S`, `E`, formalization/CN1/ChowlaSelberg/Remainder.lean:36, :40, :43). The main term is written with the coefficient as it falls out, π^s Γ(s − ½)/Γ(s) (4/(πd))^{s−½} (`CN1.CS.mainTerm`, formalization/CN1/ChowlaSelberg/MainTerm.lean:24), and the formula is

   ½ Z_d(s) = mainTerm_d(s) + E_d(s)  for Re s > 1

   (`CN1.CS.CS_main`, formalization/CN1/ChowlaSelberg/MainTerm.lean:150). The classical shape with 2^{2s−1}√π d^{½−s} is an algebraic rewriting (`CS_main_classical`, formalization/CN1/ChowlaSelberg/MainTerm.lean:218).

Holomorphy and the remainder bound. Each I(·; a, b) is holomorphic on Re s > ½ by Mathlib's Mellin machinery (`differentiableAt_I`, formalization/CN1/ChowlaSelberg/GammaIntegral.lean:164). The termwise bound from step 1 reads, at any s with Re s > ½,

  ‖(−1)^{kby} I(s; πdy²/4, πk²)‖ ≤ Γ(Re s − ½) (8/(πd))^{Re s − ½} e^{−c|y|} e^{−c|k|},  c = π√d/2,

a product of two geometric majorants in y and k (`CN1.CS.norm_Rterm_le`, formalization/CN1/ChowlaSelberg/Remainder.lean:147; the constant `cst d = π√d/2` is at formalization/CN1/ChowlaSelberg/Remainder.lean:33). The majorant is summable and locally uniform in s, so the double series is holomorphic on Re s > ½; the factor 1/Γ(s) is kept outside the sum because it is entire but not bounded on vertical strips, and E_d is then holomorphic on Re s > ½ as a product (`CN1.CS.differentiableOn_E`, formalization/CN1/ChowlaSelberg/Remainder.lean:257). The main term is holomorphic on {Re s > ½} minus the point s = 1, where ζ(2s − 1) has its pole (`differentiableOn_mainTerm`, formalization/CN1/ChowlaSelberg/MainTerm.lean:244).

At real σ every term of E_d is real, so E_d(σ) is real (`E_ofReal_im`, formalization/CN1/ChowlaSelberg/Remainder.lean:288). At σ = 7/8, summing the majorant gives

  |E_d(7/8)| ≤ B(d) := 2 π^{7/8} Γ(3/8)/Γ(7/8) · (8/(πd))^{3/8} · e^{−c}/(1 − e^{−c/2})²

(`CN1.CS.B`, formalization/CN1/ChowlaSelberg/Remainder.lean:49; `norm_E_seven_eighths_le`, formalization/CN1/ChowlaSelberg/Remainder.lean:320), and for d ≥ 7, where e^{−c/2} ≤ ¼, this is at most the simpler

  B₀(d) := 4 π^{7/8} Γ(3/8)/Γ(7/8) · (8/(πd))^{3/8} · e^{−π√d/2}

(`CN1.CS.B0`, formalization/CN1/ChowlaSelberg/Remainder.lean:54; `B_le_B0`, formalization/CN1/ChowlaSelberg/Remainder.lean:376), which is decreasing in d (`B0_antitone`, formalization/CN1/ChowlaSelberg/Remainder.lean:395). Numerically B₀(655) is about 10^{−17}, against a main term of about 10^{−3}, so there is enormous slack; the true remainder at d = 655 is about 10^{−35}.

Continuation to 7/8. The identity ½ Z_d = mainTerm_d + E_d has been proved on Re s > 1. Its right-hand side is holomorphic on {Re s > ½} ∖ {1}. If F is any function holomorphic on {Re s > ½} ∖ {1} that agrees with ½ Z_d on Re s > 1, then F = mainTerm_d + E_d on the whole connected domain, by the identity theorem, and in particular at s = 7/8. Rather than prove that a half-plane minus a point is connected (the pinned Mathlib has that only for the whole plane minus a point), the development builds an explicit open convex set V containing 7/8 and a piece of {Re s > 1} but not 1 (`CN1.CS.V`, formalization/CN1/ChowlaSelberg/Continuation.lean:36), and applies Mathlib's `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` there (`eqOn_V_of_eqOn_re_gt_one`, formalization/CN1/ChowlaSelberg/Continuation.lean:113; `eq_at_ofReal_of_differentiableOn_sdiff`, formalization/CN1/ChowlaSelberg/Continuation.lean:132). The result:

  F(7/8) = mainTerm_d(7/8) + E_d(7/8)

(`CN1.CS.CS_seven_eighths`, formalization/CN1/ChowlaSelberg/SevenEighths.lean:34). The version we actually consume takes F = ζ · L for an L holomorphic on Re s > ½ (`CN1.CS.CS_seven_eighths_zeta_mul`, formalization/CN1/ChowlaSelberg/SevenEighths.lean:56), with the main term spelled out at s = 7/8:

  ζ(7/8) · L(7/8) = ζ(7/4) + [π^{7/8} Γ(3/8)/Γ(7/8) · (4/(πd))^{3/8}] · ζ(3/4) + E_d(7/8)

(`mainTerm_seven_eighths`, formalization/CN1/ChowlaSelberg/MainTerm.lean:229), together with |Re E_d(7/8)| ≤ B₀(d) for d ≥ 7 (`abs_E_seven_eighths_re_le_B0`, formalization/CN1/ChowlaSelberg/SevenEighths.lean:78). The bracket equals 2^{3/4} √π Γ(3/8)/Γ(7/8) d^{−3/8} (`CN1.Numerics.coeff_eq`, formalization/CN1/Numerics/Glue.lean:28), which is the C d^{−3/8} of section 2, with C = 2^{3/4} √π Γ(3/8)/Γ(7/8) ≈ 6.4847.

Everything in this section is a theorem about Mathlib's `riemannZeta`, `Complex.Gamma`, `Real.Gamma`, `Real.pi`, `Real.exp`, `Real.sqrt` and real powers; the remainder bound is a theorem about the development's own E_d, not about a separately defined function. This matters: a numerical inequality about a look-alike function proves nothing about the function in the identity.

### 3e. The numerics at s = 7/8

The analytic contradiction needs four real numbers to be pinned down, as statements about Mathlib's `riemannZeta` and `Real.Gamma`: ζ(7/4), ζ(3/4), ζ(7/8) and Γ(3/8)/Γ(7/8). Two of the zeta values are left of the line Re s = 1, where the Dirichlet series does not converge, so the first task is a representation of ζ valid for Re s > 0.

ζ on Re s > 0. Mathlib's `riemannZeta₁ s = (s − 1) ζ(s)` is entire. Define

  w(a, s) = s (a^{1−s} − (a+1)^{1−s}) − (s − 1) a (a^{−s} − (a+1)^{−s}),  W(s) = Σ_{n≥0} w(n+1, s)

(`CN1.Numerics.w`, `W`, formalization/CN1/Numerics/ZetaStrip.lean:42 and :47). For Re s > 1 the series telescopes against the Dirichlet series and gives (s − 1)ζ(s) = s − W(s); each w(a, s) is O(a^{−Re s − 1}), so W is holomorphic on Re s > 0, and the identity theorem on that convex half-plane extends the equation (`riemannZeta₁_eq_sub_W`, formalization/CN1/Numerics/ZetaStrip.lean:255; `riemannZeta_eq_of_pos_re`, formalization/CN1/Numerics/ZetaStrip.lean:277). For real σ > 0, σ ≠ 1, this gives ζ(σ) as a real number (`riemannZeta_ofReal_eq`, formalization/CN1/Numerics/ZetaReal.lean:58).

Euler–Maclaurin with a one-sided remainder. Integrating by parts on each unit interval and telescoping the tail produces, for every M,

  ζ(σ) = Σ_{n<M} (n+1)^{−σ} + (M+1)^{1−σ}/(σ − 1) + (M+1)^{−σ}/2 + R,  0 ≤ R ≤ σ(σ+2)/8 · (M+1)^{−σ−1}

(`CN1.Numerics.riemannZeta_ofReal_eulerMaclaurin`, formalization/CN1/Numerics/ZetaReal.lean:304). With M = 1000 the finite sums are brackets of exact rationals: 1000-term sums at scale 10^{−10}, generated by a script and checked by the kernel with `decide +kernel` (formalization/CN1/Numerics/ZetaTables.lean, generated). The outcomes:

- ζ(3/4) ∈ [−3.44129, −3.44128] (`CN1.Numerics.riemannZeta_three_quarters`, formalization/CN1/Numerics/ZetaValues.lean:108);
- ζ(7/8) ∈ [−7.432, −7.4319] (`riemannZeta_seven_eighths`, formalization/CN1/Numerics/ZetaValues.lean:119);
- ζ(7/4) ∈ [1.96232, 1.9623202] (`riemannZeta_seven_quarters`, formalization/CN1/Numerics/ZetaValues.lean:130);

each in the form "there is a real r with riemannZeta(q) = r and r in the interval", so that they substitute directly into the complex identity. The two signs we need are corollaries: ζ(3/4) < 0 (`riemannZeta_three_quarters_re_neg`, formalization/CN1/Numerics/ZetaValues.lean:141) and ζ(7/8) < 0 (`riemannZeta_seven_eighths_re_neg`, formalization/CN1/Numerics/ZetaValues.lean:146), and ζ(7/8) is real (`riemannZeta_seven_eighths_im`, formalization/CN1/Numerics/ZetaValues.lean:155). For comparison, ball arithmetic gives ζ(3/4) = −3.44128538694522…, ζ(7/8) = −7.43196132932515…, ζ(7/4) = 1.96232009945134….

The Gamma ratio. Mathlib has log-convexity of Γ (`Real.convexOn_log_Gamma`), which yields two-sided estimates of the Bohr–Mollerup kind, Γ(n+1)(n+x)^{x−1} ≤ Γ(n + x) ≤ Γ(n) n^x for 0 < x < 1 (formalization/CN1/Numerics/GammaBounds.lean). Writing Γ(3/8)/Γ(7/8) = [Γ(n + 3/8)/Γ(n + 7/8)] · Π_{k<n} (k + 7/8)/(k + 3/8) with n = 8000, the ratio of shifted Gammas is bracketed to relative width about 4·10^{−5} and the product is a ratio of two exact integers of about 35,000 digits, which the kernel multiplies out. The result is

  2.1753 ≤ Γ(3/8)/Γ(7/8) ≤ 2.1755

(`CN1.Numerics.Gamma_ratio_enclosure`, formalization/CN1/Numerics/GammaRatio.lean:167; the true value is 2.1754059…).

The threshold. Define, for real d,

  M(d) = ζ(7/4) + 2^{3/4} √π (Γ(3/8)/Γ(7/8)) d^{−3/8} ζ(3/4),  B₀(d) as in 3d

(`CN1.Numerics.mainTerm`, `B0`, formalization/CN1/Numerics/Threshold.lean:38 and :44). Then M(655) ≥ 0.00104 (`mainTerm_655_ge`, formalization/CN1/Numerics/Threshold.lean:90; the enclosure actually gives M(655) ∈ [0.00105, 0.00124], and ball arithmetic gives 0.00113790742…), B₀(655) ≤ 3·10^{−16} (`B0_655_le`, formalization/CN1/Numerics/Threshold.lean:119), M is increasing for d ≥ 655 because ζ(3/4) < 0 (`mainTerm_mono`, formalization/CN1/Numerics/Threshold.lean:159), and B₀ is decreasing (`B0_anti`, formalization/CN1/Numerics/Threshold.lean:176). Hence

  M(d) − B₀(d) > 0 for every real d ≥ 655

(`CN1.Numerics.mainTerm_sub_B0_pos`, formalization/CN1/Numerics/Threshold.lean:198), and therefore, for an integer d ≡ 0 or 3 (mod 4): if M(d) − B₀(d) ≤ 0 then d ≤ 652 (`disc_le_652_of_mainTerm_nonpos`, formalization/CN1/Numerics/Threshold.lean:206; the integers 653 and 654 are excluded by the congruence, which is why the bound is 652 and not 654).

Two numbers that are not in the Lean proof but explain the shape of the result. The main term's zero is at d* = 653.98763…, so M(652) = −0.0022412 < 0 and M(655) = +0.0011379 > 0 (ball arithmetic, `computations/arb_threshold.py` in this repository; the values are certified as balls). The method genuinely cannot exclude d = 652 by itself: the finite step has to do that. The margin at 655 is about 10^{−3} against a remainder of about 10^{−35}, so there was room to be crude about the remainder and about the Gamma ratio and still win comfortably.

The glue lemma that connects these numerics to the Chowla–Selberg identity in its own notation, and performs the whole analytic contradiction of 3f, is `CN1.Numerics.disc_le_652_of_CS` (formalization/CN1/Numerics/Glue.lean:74). Its hypotheses are: d ≡ 0 or 3 (mod 4); d ≥ 7; a function L holomorphic on Re s > ½; the identity ζ(s) L(s) = ½ Z_d(s) on Re s > 1; and L(7/8) real and ≥ 0. Its conclusion is d ≤ 652.

### 3f. Positivity: L(7/8, χ) ≥ 0, hence d ≤ 652

This is the step that uses the deep input, and it uses it exactly once.

The theorem from openai/math (family 003) is, in Mathlib's vocabulary: for every modulus q ≠ 0, every Dirichlet character χ mod q, and every s with Re s > 7/8 such that it is not the case that χ = 1 and s = 1, one has L(s, χ) ≠ 0 (`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`, openai/math at commit adc7f124, file lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean:19). The function `DirichletCharacter.LFunction` there is Mathlib's, the same one that appears in 3c.

Let χ be a Dirichlet character whose values are real (every quadratic character qualifies: `MulChar.IsQuadratic.conj_apply`, formalization/CN1/Assembly/Positivity.lean:40). Then L(χ, s̄) = conj L(χ, s) away from the pole of the trivial character: it holds termwise on Re s > 1 and extends by the identity principle, in the same way Mathlib proves `riemannZeta_conj` (`CN1.LFunction_conj`, formalization/CN1/Assembly/Positivity.lean:57). So L(χ, σ) is real for real σ (`CN1.LFunction_ofReal_im`, formalization/CN1/Assembly/Positivity.lean:90).

Positivity for σ > 1 needs no Euler product: L(χ, x) → χ(1) = 1 as x → +∞ (Mathlib's `LSeries.tendsto_atTop`), so Re L(χ, x) > 0 at some real x > 1 (`exists_one_lt_and_LFunction_re_pos`, formalization/CN1/Assembly/Positivity.lean:107); a continuous real function on an interval that never vanishes and is positive somewhere is positive everywhere (`pos_on_of_continuousOn_of_ne_zero`, formalization/CN1/Assembly/Positivity.lean:121); and L(χ, σ) ≠ 0 for σ > 1 is Mathlib's `LFunction_ne_zero_of_one_le_re`. Hence L(χ, σ) > 0 for σ > 1 (`CN1.LFunction_ofReal_re_pos_of_one_lt`, formalization/CN1/Assembly/Positivity.lean:139).

Now replace Mathlib's non-vanishing by openai/math's. For χ ≠ 1 the same sign-propagation argument on the interval (7/8, ∞) gives L(χ, σ) > 0 for every real σ > 7/8 (`CN1.LFunction_ofReal_re_pos_of_seven_eighths_lt`, formalization/CN1/Assembly/Positivity.lean:152), and by continuity from the right,

  L(χ, 7/8) is real and L(χ, 7/8) ≥ 0

(`CN1.LFunction_seven_eighths_nonneg`, formalization/CN1/Assembly/Positivity.lean:166; the quadratic-character form that the assembly uses is `LFunction_seven_eighths_nonneg_of_isQuadratic`, formalization/CN1/Assembly/Positivity.lean:191). Note that ≥ 0 is the honest conclusion; the zero-free region is open at 7/8, and nothing here rules out L(7/8, χ) = 0. The argument does not need more.

The contradiction. Take χ = χ_{−d} for our field with class number one and m ∉ {1, 3}, so d ≥ 7 (`CN1.Assembly.seven_le_disc`, formalization/CN1/Assembly/Core.lean:47). By 3b–3c, ζ(s) L(s, χ) = ½ Z_d(s) on Re s > 1; L(·, χ) is entire because χ ≠ 1 (Mathlib's `DirichletCharacter.differentiable_LFunction`); so 3d gives

  ζ(7/8) · L(7/8, χ) = M(d) + E_d(7/8),  |E_d(7/8)| ≤ B₀(d).

The left side is ≤ 0: ζ(7/8) < 0 by 3e and L(7/8, χ) ≥ 0 by this section. The right side is ≥ M(d) − B₀(d). So M(d) − B₀(d) ≤ 0, and by 3e, d ≤ 652. In Lean this is `CN1.Numerics.disc_le_652_of_CS` applied with L = L(·, χ_{−d}), and the wrapper that supplies χ's properties from 3a is `CN1.Assembly.disc_le_652_of_epstein` (formalization/CN1/Assembly/Core.lean:59), whose only hypotheses are m squarefree, m ≠ 1, m ≠ 3, and the Epstein identity of 3b–3c as a proposition about m (`CN1.Assembly.EpsteinIdentity`, formalization/CN1/Assembly/Core.lean:53).

### 3g. The finite range: split-prime witnesses

We now know that a class-number-one field outside the nine would have d ≤ 652. It remains to show that no squarefree m outside the nine with d ≤ 652 gives class number one. The argument is Rabinowitsch-style.

The elementary inequality. Write the principal form as Q(x, y) = x² + txy + cy² with t ∈ {0, 1} and 4c − t² = d (`CN1.Finite.tOf`, `cOf`, `dOf`, formalization/CN1/Finite/Params.lean:19, :22, :25; these agree with the foundations' `disc` and `principalForm`: `CN1.Finite.disc_eq_dOf`, formalization/CN1/Finite/Bridge.lean:24, and `principalForm_eq`, formalization/CN1/Finite/Bridge.lean:26). Then 4Q(x, y) = (2x + ty)² + d y². If y ≠ 0 this is at least d, with equality only when 2x + ty = 0 and y = ±1. For t = 1 that is impossible by parity, so 4Q ≥ d + 1. For t = 0 it happens exactly at (0, ±1), where Q = c = d/4. And if y = 0 then Q = x² is a square. Therefore: a prime p with 4p ≤ d and p ≠ c is not a value of Q (`CN1.Finite.not_form_eq_prime`, formalization/CN1/Finite/Elementary.lean:41). The condition 4p ≤ d is the same as p < (d + 1)/4 for integers.

Why "split" and not merely "small". The proviso p ≠ c is essential and is exactly the difference between a split prime and a prime that merely has a degree-one prime above it. Take d = 8, the field ℚ(√−2), which does have class number one. The prime 2 is ramified, 2 < (8 + 1)/4, and the principal form x² + 2y² represents 2 at (0, ±1). So "a prime below (d + 1)/4 with a degree-one prime above it" does not force h ≠ 1. A split prime p satisfies p ∤ d, hence p ≠ d/4 = c, and the inequality applies. Among the 197 fundamental discriminants with 4 < d ≤ 652, 136 have a ramified prime below the bound, so a proof that checked only "p does not divide d" or only "p has a degree-one prime above it" would have been wrong; d = 8 is the one case in range where the distinction bites, but one is enough.

The lemma. Suppose 𝓞_K = ℤ[θ] with minimal polynomial X² − tX + c and norm form x² + txy + cy² (the interface `CN1.Finite.QuadInt`, formalization/CN1/Finite/SplitPrime.lean:35, instantiated from 3a by `quadIntOfFoundations`, formalization/CN1/Finite/Bridge.lean:38). If p is prime, y² − ty + c ≡ 0 (mod p) for some integer y, 4p ≤ d and p ≠ c, then the class number is not one (`CN1.Finite.classNumber_ne_one_of_witness`, formalization/CN1/Finite/SplitPrime.lean:72). The proof: by Kummer–Dedekind the factor X − y of the minimal polynomial mod p corresponds to a prime P above p of inertia degree one, so N(P) = p; if 𝓞_K were a principal ideal ring, P = (β) with |N(β)| = p, β = x + y′θ, and Q(x, y′) = p, contradicting the inequality. The hypothesis "y² − ty + c has a root mod p" is what the kernel can check per instance; for p ∤ d it is equivalent to χ(p) = 1 by 3a, but the finite part does not need to know that.

The 190 instances. For each squarefree m outside the nine with d ≤ 652 we need a prime p and a residue y. The predicate `CN1.Finite.IsWitness m p y` (formalization/CN1/Finite/SplitPrime.lean:129) bundles: p prime, p | y² − ty + c, 4p ≤ d, p ≠ c, all over ℕ so that it is decidable. The instances were found by a script and are checked by the kernel one by one: primality by `norm_num`'s certificate, the rest by `decide`. A typical one is m = 5, d = 20, p = 3, y = 1 (`CN1.Finite.w_5`, formalization/CN1/Finite/Witnesses/Chunk1.lean:9). The 190 instances are split into four generated files for compile-time reasons: m from 5 to 93 (50 instances), 94 to 211 (50), 215 to 451 (50), and 455 to 651 (40). Of the 190, 127 have d ≡ 3 (mod 4) (so d = m ≤ 651) and 63 have d = 4m (so m ≤ 163). The least split prime is p = 2 for 67 of them, p = 3 for 48, p = 5 for 31, p = 7 for 18, p = 11 for 10, p = 13 for 7, p = 17 for 3, p = 19 for 2, p = 23 for 3, and the largest least split prime is p = 31, at m = 58 (d = 232). The seven discriminants in range with no split prime below the bound are exactly d = 7, 8, 11, 19, 43, 67, 163, the Heegner discriminants above 4; this agrees with two independent class-number computations (reduced forms and Dirichlet's formula), neither of which is used in the proof.

The list of 190 radicands is `CN1.Finite.nonHeegner190` (formalization/CN1/Finite/Witnesses.lean:21), of kernel-checked length 190 (`length_nonHeegner190`, formalization/CN1/Finite/Witnesses.lean:23), and `exists_witness_of_mem` (formalization/CN1/Finite/Witnesses.lean:25) collects the instances. The range lemma says every m < 653 with no square factor k² for 2 ≤ k ≤ 26, with d ≤ 652 and outside the nine, is on the list (`mem_nonHeegner190`, formalization/CN1/Finite/Witnesses.lean:32), by `decide +kernel`; the predicate "no square factor up to 26²" (`SqfBelow`, formalization/CN1/Finite/SplitPrime.lean:147) is a kernel-friendly consequence of `Squarefree` since 26² = 676 > 652. Assembled, for squarefree m with d ≤ 652 outside the nine, the class number is not one (`classNumber_ne_one_of_quadInt`, formalization/CN1/Finite/Witnesses.lean:38), and in terms of the statement's own hypotheses, `CN1.Finite.classNumber_ne_one_of_foundations` (formalization/CN1/Finite/Bridge.lean:54).

### 3h. The converse: the nine fields have class number one

For the nine fields we use the Minkowski bound. Mathlib's `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime` says 𝓞_K is a principal ideal ring if every nonzero prime ideal of norm at most the Minkowski bound is principal. For a quadratic field with |disc K| ≤ d, the bound is (4/π)^{r₂} (2!/2²) √|disc K| ≤ (2/3)√d, using only r₂ ≤ 1 and π > 3 (`CN1.Finite.le_two_thirds_sqrt_of_le_minkowski`, formalization/CN1/Finite/Converse.lean:31). A maximal ideal P with residue characteristic q has N(P) = q, or N(P) = q² and P = (q), which is principal (`absNorm_maximal_cases`, formalization/CN1/Finite/Converse.lean:74). So what has to be excluded is a prime of norm q with q ≤ (2/3)√d. If θ ∈ 𝓞_K satisfies θ² = tθ − c and z² − tz + c has no root mod q, then 𝓞_K/P ≅ 𝔽_q would contain a root, so no such P exists (`not_absNorm_eq_of_no_root`, formalization/CN1/Finite/Converse.lean:110). For m ≡ 3 (mod 4) the element θ = (1 + α)/2 is built directly (`exists_theta`, formalization/CN1/Finite/Converse.lean:134).

The cases: for d ∈ {3, 4, 7, 8} the bound (2/3)√d is below 2, so there is nothing to check. For d = 11, 19: q = 2, and z² − z + 3, z² − z + 5 have no root mod 2. For d = 43: q ∈ {2, 3} against z² − z + 11. For d = 67: q ∈ {2, 3, 5} against z² − z + 17. For d = 163: q ∈ {2, 3, 5, 7} against z² − z + 41. Each "no root" is a `decide` over ZMod q. The theorem is `CN1.Finite.classNumber_eq_one_of_mem_nine` (formalization/CN1/Finite/Converse.lean:160), with hypothesis |disc K| ≤ d, which 3a's `discr_eq` supplies; the version in the statement's own terms is `CN1.Finite.classNumber_eq_one_of_foundations` (formalization/CN1/Finite/Bridge.lean:62). This direction covers m = 1 and m = 3 too, which is why the analytic half never needed them.

### 3i. The assembly

The main theorem is proved in two layers. The first, `CN1.Assembly.classNumber_eq_one_iff_of_epstein` (formalization/CN1/Assembly/Core.lean:72), is the statement of record with one extra hypothesis hE: whenever the class number is one and m ∉ {1, 3}, the Epstein identity holds for m. Its proof is short enough to read in full:

- the direction ⇐ is `Finite.classNumber_eq_one_of_foundations` (3h);
- for ⇒, assume class number one and, for contradiction, m outside the nine; then m ≠ 1 and m ≠ 3; `disc_le_652_of_epstein` (3d–3f, fed by hE) gives d ≤ 652; and `Finite.classNumber_ne_one_of_foundations` (3g) gives the contradiction.

The second layer, `CN1.classNumber_eq_one_iff` (formalization/CN1/Main.lean:36), discharges hE with `CN1.Epstein.epstein_identity_Z` (3b–3c). The conditional form is kept on record so that a reader can see exactly which hypothesis the number-field steps supply to the analytic steps, and because the four negative controls of section 4 are built on top of it.

The dependency picture is clean. The foundations, the Epstein identity, Chowla–Selberg and the numerics import nothing outside Mathlib and this development. The finite part imports only Mathlib and the foundations. The positivity module imports openai/math's non-vanishing theorem. The 7/8 theorem is used in exactly one place, 3f, through `LFunction_ne_zero_of_seven_eighths_lt_re`.

## 4. How it was checked

The main theorem was built with `lake build` in the pinned environment (Lean v4.34.1, Mathlib at commit d13f23b, which is the environment of openai/math's 7/8 theorem), and `#print axioms CN1.classNumber_eq_one_iff` reports exactly `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, `axiom`, `native_decide` or `admit` anywhere in the solution library. Each part of the development was also axiom-audited on its own as it was built.

Comparator. The artefact was then checked with Comparator (leanprover/comparator, tag v4.34.0, running under toolchain v4.34.1), the tool openai/math uses for its own challenges. Comparator builds the challenge module (the statement with `sorry`, importing only Mathlib) and the solution module, exports both constant closures with lean4export, compares the elaborated statements for syntactic equality, checks that the solution's axioms are within the permitted set, and then replays the solution export through two kernels: nanoda, an independent reimplementation of Lean's type checker, and Lean's own default kernel. The run of record was made from a frozen source tree (every source file's md5 recorded before the run, re-checked after, unchanged), with the build products of the last two modules deleted beforehand so that Comparator's own build recompiled them from the recorded sources. Its verdict: "nanoda kernel accepts the solution", "Lean default kernel accepts the solution", "Your solution is okay!"; about 548 seconds of wall time and 9.2 GB of memory. An earlier run on a tree that had moved by one additive, unused lemma during the run gave the same verdict; the frozen run is the one we cite.

The published files. Before publication, internal references were removed from the comments of the Lean files; nothing else changed. A comment-stripping script compared every published Lean module (all 45) with the file that was checked, and with comments removed the two are identical, byte for byte. Comparator was then run again, in the same way, on exactly the Lean modules and Comparator configurations in this repository, built against the same patched dependency tree as the run of record. Again both kernels accepted the proof, and both tampered statements below were rejected.

Negative controls. A checker that accepts everything is worthless, so four deliberately wrong inputs were run through the same pipeline against the frozen tree. All four were rejected.

- (a) The challenge statement with the hypothesis `Squarefree m` deleted (a false statement, see section 1), against the real proof: rejected, "Challenge and solution theorem statement do not match".
- (b) The challenge statement with 163 replaced by 167 (false: ℚ(√−167) has class number 11), against the real proof: rejected, statement mismatch.
- (c) The real challenge against a "proof" that derives the statement from a postulated axiom "every squarefree m has d ≤ 652", which is false (m = 1000003 is a counterexample) but makes the rest of the argument go through: rejected, "Illegal axiom detected: 'CN1.Assembly.fake_bound'".
- (c′) The same false bound discharged by `sorry` instead of an axiom: rejected, "Illegal axiom detected: 'sorryAx'".

The tampered statements (a) and (b) are in this repository, with their Comparator configurations, so anyone can rerun them. The two tampered proofs (c) and (c′) are not published, because a file that declares a false axiom has no business in a public library; their logs are available on request.

Comparator cannot show that a false statement is unprovable; what the controls show is that a changed statement does not pass as the real one, and that an unproved or postulated input does not pass as a proof. The controls live in a separate library that no build of the solution ever compiles, and the dependency audit confirms that none of their constants are in the main theorem's closure.

The dependency audit. A script walked the transitive closure of `CN1.classNumber_eq_one_iff` through types, proof terms and definition bodies (an earlier version that walked only definition bodies and missed theorem proofs was caught and replaced; the fact is recorded). The closure has 129,170 constants: Mathlib 92,527; openai/math (`OAI`) 26,740, from 2,656 modules, all of them under `OAI.NumberTheory.DirichletL`, which is family 003; Lean core (`Init`, `Std`, `Lean`) 8,091; this development (`CN1`) 1,028; and 566 from two packages that openai/math's own proof imports, `PrimeNumberTheoremAnd` (375; the Wiener–Ikehara and Sobolev material) and `RellichKondrachov` (191), at the commits pinned by openai/math (adc7f124, with PrimeNumberTheoremAnd at c39a7511 and rellich-kondrachov at 70f85d4c, each with OpenAI's published Lean-v4.34.1 compatibility patch, verified to apply); plus Mathlib's dependencies `Batteries` (215) and `Aesop` (3). So the 7/8 theorem's proof is inside what was checked, not a hypothesis. A case-insensitive scan of every constant and module name in the closure for heegner, baker, stark, gross, zagier, goldfeld, heilbronn, deuring, linfoot, class number one and its spellings found no declaration or module named after any of them except this development's own names (the main theorem, the converse lemmas and the list `nonHeegner190`) and Mathlib's `NumberField.classNumber_eq_one_iff`, which is the criterion "class number one iff principal ideal ring", not a classification. No classification of class-number-one fields is anywhere in the closure. The 190 witness primes, the three zeta enclosures, the Gamma enclosure and the threshold were all produced by scripts and then accepted or rejected by the kernel alone; none of the script output is trusted.

Independent review. An independent AI review session, separate from the sessions that wrote the proof, reviewed the statement before the assembly that proves it was built, and read every module of the development in full before the run of record. The numerics (the threshold, the prefactor of the remainder, the witness list) were recomputed independently with separate code. Two points in the record show why that matters. The review caught the wrong prefactor described in 3d. The d = 8 example in 3g, which is why the finite lemma must require a split prime and not just a small one, was flagged while the witnesses were being computed and then confirmed by the review.

Caveats. The Comparator runs described here are local and unsandboxed: the sandboxing layer that Comparator normally uses was replaced by a pass-through shim on this machine, as in our earlier replay of openai/math's own 7/8 challenge. An independent replay by a separate AI review session accepted the proof under both kernels. The replay used its own build of this project's modules and its own build of nanoda, against the same verified dependency tree, with the same Comparator and lean4export binaries, on the same machine; it was local and not sandboxed. It also rejected two further tampers: the statement with 163 removed from the list, and a proof routed through `native_decide`. Its independent audit of the dependency closure agrees with ours. A clean copy of the repository's formalization/ directory, with no build state and following the published build instructions, also completes all 11,914 build jobs, and the main theorem reports only the three standard axioms. The md5 of every file in the frozen tree, and the hashes of the three tool binaries, are available on request, with the logs.

## 5. What is not claimed

The bound d ≤ 652 is effective and is proved in Lean, but it rests on openai/math's theorem that Dirichlet L-functions do not vanish for Re s > 7/8. That theorem's manuscript is, as far as we know, not refereed. Its Lean proof has been kernel-checked, here and in our earlier replay, so its correctness is not in question in the sense that matters for the kernel; what a human reader may reasonably want, and does not yet have, is a refereed understanding of why it is true. We are explicit about this because the point of the exercise is to separate what is mechanically certain from what is understood.

Nothing here bears on the Riemann hypothesis. The class number one problem is about the real zeros of Dirichlet L-functions of real characters near s = 1 (Siegel zeros), and the input we use is a zero-free half-plane, not anything about ζ on the critical line.

The proof is not optimal and does not try to be. The remainder bound B₀(655) ≈ 10^{−17} is about fourteen orders of magnitude below the margin it has to beat; the Gamma ratio is enclosed to five digits where two would do; the Minkowski argument for the nine uses (2/3)√d rather than (2/π)√d. These choices made the Lean proof shorter, not the mathematics sharper. The quantity that is sharp is the threshold itself: the method, with this main term, cannot exclude d = 652, and the finite step is genuinely needed up to there.

The Chowla–Selberg module is specific to the principal form with a = 1, which is all that class number one requires. It is not a general Chowla–Selberg formula for arbitrary binary quadratic forms.

Finally, this note describes the mathematics and the checking; it is not itself checked by anything. Where it says what a Lean lemma states, the lemma is the authority.

## 6. Credits

- The quasi-Riemann hypothesis at 7/8 for all Dirichlet L-functions: OpenAI, openai/math, family 003 (Apache-2.0).
- The non-existence of Siegel zeroes and its digests: OpenAI; W. D. Banks (arXiv:2610.15483); B. Kerr (arXiv:2610.21099); B. Green.
- The Chowla–Selberg formula: S. Chowla and A. Selberg. In the comments of Tao's post, michaelmross gave the expansion of the principal form by Poisson summation, Tao observed that together with the 7/8 theorem it gives d < 655, and LemmaLab evaluated it at the fixed point s = 7/8 and certified d ≤ 653 in ball arithmetic. Section 3e is that evaluation, proved in Lean.
- The finite step is classical, in the spirit of Rabinowitsch's criterion. In the thread it was used by Lior Silberman (under class number one every small prime is inert), Kyle Pratt, twinheterodox and michaelmross.
- The challenge: T. Tao.
- Mathlib, for the number-field, L-series, Gamma, Mellin and Poisson-summation infrastructure that the development leans on throughout, and the Lean 4 kernel; nanoda, for the second kernel; leanprover/comparator and lean4export for the checking pipeline.

This work was done with extensive use of AI assistance (Anthropic's Claude), in several separate sessions, with the writing and the reviewing in different sessions. The mathematical claims are kernel-checked; the history, the attributions and the account of how the work was checked are ours.
