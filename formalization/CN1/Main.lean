import CN1.Assembly.Core
import CN1.Epstein.Bridge

/-!
# The class number one theorem for imaginary quadratic fields (solution side)

Pinned environment: Lean v4.34.1, Mathlib d13f23b (the openai/math 7/8 environment).

`CN1.classNumber_eq_one_iff` is the statement of the Comparator challenge
`CN1Challenges.ClassNumberOne`, proved without Heegner, Baker or Stark, in six steps:

1. (`CN1.Epstein.Lattice`) `h_K = 1`, `m ∉ {1, 3}` ⇒ `ζ_K(s) = ½ Σ′ Q(x,y)^{-s}` on `Re s > 1`;
2. (`CN1.Epstein.Factorization`) `ζ_K(s) = ζ(s) · L(s, χ_{-d})`;
3. (`CN1.ChowlaSelberg`) Chowla–Selberg with an explicit remainder, continued to `s = 7/8`;
4. (`CN1.Numerics`) certified enclosures of `ζ(7/4)`, `ζ(3/4)`, `ζ(7/8)`, `Γ(3/8)/Γ(7/8)`, and
   the threshold `M(d) - B₀(d) > 0` for `d ≥ 655`;
5. (`CN1.Assembly.Positivity`) `L(7/8, χ_{-d}) ≥ 0`, from openai/math's zero-free region
   `Re s > 7/8` for Dirichlet L-functions; with `ζ(7/8) < 0` this forces `d ≤ 652`;
6. (`CN1.Finite`) the finite Rabinowitsch search for `d ≤ 652`, and the Minkowski-bound
   converse for the nine.

`CN1.Assembly.Core` assembles 3–6 with the identity of 1–2 as a hypothesis; this file discharges
it with `CN1.Epstein.epstein_identity_Z`.
-/

set_option autoImplicit false

open NumberField

namespace CN1

/-- **Class number one for imaginary quadratic fields.** Let `K` be a number field of degree two
over `ℚ` containing a square root of `-m`, where `m` is a squarefree natural number (so `m ≥ 1`
and `K ≅ ℚ(√-m)`). Then the class number of `K` is one if and only if
`m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}`. -/
theorem classNumber_eq_one_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ) := by
  obtain ⟨α, hα⟩ := hsq
  exact Assembly.classNumber_eq_one_iff_of_epstein K hK m hm ⟨α, hα⟩
    fun h1 hm1 hm3 s hs => Epstein.epstein_identity_Z hα hK hm hm1 hm3 h1 hs

end CN1
