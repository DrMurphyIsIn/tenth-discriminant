import Mathlib

/-!
# CN-1 Comparator challenge: the class number one theorem for imaginary quadratic fields

Statement only (`sorry`); the proof is the solution side. The import closure is Mathlib alone
(Lean v4.34.1, Mathlib d13f23b, the openai/math 7/8 environment). Trust base: this statement, the
Mathlib definitions it uses (`NumberField`, `NumberField.classNumber`, `Module.finrank`,
`Squarefree`), the Lean kernel and nanoda, and the axioms `propext`, `Classical.choice`,
`Quot.sound`.

Classical theorem (Heegner 1952, Baker 1966, Stark 1967): the imaginary quadratic fields
`ℚ(√-m)`, `m ≥ 1` squarefree, with class number one are exactly those with
`m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}`. The intended proof (see the README) is Heegner-free: zero-free
region `Re s > 7/8` for Dirichlet L-functions, Chowla–Selberg, and a finite Rabinowitsch search.

Conventions. `m` is the radicand, not the discriminant: `|disc ℚ(√-m)| = m` if `m ≡ 3 (mod 4)`
and `4m` otherwise, so the nine fields have `|disc| ∈ {4, 8, 3, 7, 11, 19, 43, 67, 163}`.
`Squarefree m` forces `m ≠ 0`, and `-m` is not a square in `ℚ` for `m ≥ 1`, so `α` below is
irrational and `K = ℚ(α) ≅ ℚ(√-m)`.
-/

open NumberField

namespace CN1

/-- **Class number one for imaginary quadratic fields.** Let `K` be a number field of degree two
over `ℚ` containing a square root of `-m`, where `m` is a squarefree natural number (so `m ≥ 1`
and `K ≅ ℚ(√-m)`). Then the class number of `K` is one if and only if
`m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}`. The set is written out so that the statement's constant
closure is Mathlib's alone (Comparator compares every constant the statement uses). -/
theorem classNumber_eq_one_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ) := by
  sorry

end CN1
