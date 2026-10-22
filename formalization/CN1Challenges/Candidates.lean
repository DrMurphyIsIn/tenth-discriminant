import Mathlib

/-!
# Candidate statements of the class number one theorem (type-check only)

Three Mathlib-only formulations of: for squarefree `m ≥ 1`,
`classNumber ℚ(√-m) = 1 ↔ m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}`.
Every proof is `sorry`: this file exists to show the statements elaborate in the pinned
environment (Lean v4.34.1, Mathlib d13f23b). Candidate C is the statement adopted for the challenge.
-/

open NumberField Polynomial

namespace CN1.Candidates

/-- The nine Heegner radicands, as a `Finset ℕ`. -/
abbrev heegnerRadicands : Finset ℕ := {1, 2, 3, 7, 11, 19, 43, 67, 163}

/-- **Candidate A (concrete field).** `K = AdjoinRoot (X ^ 2 + C m)` over `ℚ`. The `NumberField`
instance (Mathlib/NumberTheory/NumberField/Basic.lean:449) needs `Fact (Irreducible f)`, so the
fact has to be a hypothesis of the statement; it is always true for `m ≥ 1` but a reader must
check that it is satisfiable. -/
theorem candidateA (m : ℕ) (hm : Squarefree m)
    [Fact (Irreducible (X ^ 2 + C (m : ℚ)))] :
    classNumber (AdjoinRoot (X ^ 2 + C (m : ℚ))) = 1 ↔ m ∈ heegnerRadicands := by
  sorry

/-- **Candidate B (abstract field, discriminant).** `K` any totally complex number field of degree
two; the answer is read off `NumberField.discr K`. No radicand appears. -/
theorem candidateB (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    classNumber K = 1 ↔
      discr K ∈ ({-3, -4, -7, -8, -11, -19, -43, -67, -163} : Finset ℤ) := by
  sorry

/-- **Candidate C (abstract field, radicand; RECOMMENDED).** `K` any number field of degree two
over `ℚ` containing a square root of `-m` with `m` squarefree (so `m ≥ 1` and `K ≅ ℚ(√-m)`). -/
theorem candidateC (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ heegnerRadicands := by
  sorry

/-- Sanity check on the statement's side conditions: `Squarefree m` forces `m ≠ 0`, and `-m` is
never a square in `ℚ` for `m ≥ 1`, so Candidate A's `Fact` is satisfiable and Candidate C's
`α` is irrational. (PROVED here, trivially; included so a reader can see the side conditions.) -/
theorem squarefree_ne_zero_and_not_isSquare_neg (m : ℕ) (hm : Squarefree m) :
    m ≠ 0 ∧ ¬ IsSquare (-(m : ℚ)) := by
  refine ⟨hm.ne_zero, not_isSquare_of_neg ?_⟩
  have : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm.ne_zero
  linarith

end CN1.Candidates
