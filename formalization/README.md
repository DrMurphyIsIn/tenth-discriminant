# formalization/

The Lean 4 development lives here. It is pinned to Lean v4.34.1 and the Mathlib revision used by
[openai/math](https://github.com/openai/math), which provides the zero-free region Re s > 7/8 for Dirichlet L-functions.

## The statement (reviewed; no proof yet)

[`CN1Challenges/ClassNumberOne.lean`](CN1Challenges/ClassNumberOne.lean) states the theorem, with its proof left as `sorry`:

```lean
theorem CN1.classNumber_eq_one_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)
```

It uses only Mathlib definitions, so a reader can check what it says without reading any of our code. Every imaginary quadratic
field ℚ(√−m) satisfies the hypotheses, and the hypotheses force K ≅ ℚ(√−m). An independent AI review session (see the AI-use section of the top-level README) checked this
before any proof work began, including a kernel-checked lemma that the hypotheses are satisfiable for every squarefree m.

Dropping `Squarefree m` would make the statement false: m = 4 with K = ℚ(i) is a counterexample. That gives one of the tampered
statements the finished proof must fail against.

## Comparator

[`comparator/ClassNumberOne.json`](comparator/ClassNumberOne.json) is the Comparator configuration: it uses the challenge module
above and the solution module `CN1.Main` (not yet written), checks with both Lean's kernel and nanoda, and permits only the axioms
propext, Quot.sound and Classical.choice.

## Still to come

One module per step of the argument in the top-level README: positivity of L(σ, χ) above 7/8, the Epstein/Dedekind identity,
Chowla–Selberg with an explicit remainder, the numerical inequalities, the finite range, and the assembly.
