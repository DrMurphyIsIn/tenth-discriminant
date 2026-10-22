import Lake

open System Lake DSL

/-!
Lean project for the Heegner-free proof of the class number one theorem for imaginary quadratic
fields (`CN1.classNumber_eq_one_iff` in `CN1/Main.lean`).

The one dependency is openai/math at the pinned commit. It brings Lean v4.34.1, Mathlib `d13f23b`
and OpenAI's zero-free region `Re s > 7/8` for Dirichlet L-functions
(`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`), the only declaration from
outside Mathlib and this project that our code cites directly. Every other package in `lake-manifest.json` is a dependency of
openai/math at the revision openai/math pins.

openai/math ships Lean-v4.34.1 compatibility patches for 23 of those packages
(`lean/patches/*-lean4341.patch`). Its lakefile applies them only when openai/math is the root
project, not when it is a dependency, so here they are applied by `scripts/apply_oai_patches.sh`,
which must run once before the first `lake build` (see the header of that script).
-/

package CN1 where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require OAI from git
  "https://github.com/openai/math" @ "adc7f1241b42e322a6451854ab7e4b4c146bf78a" / "lean"

/-- The challenge side: the statement with `sorry`, importing Mathlib only. Its tampered variants
under `CN1Challenges/Tamper/` are negative controls for the Comparator. -/
lean_lib CN1Challenges where
  globs := #[`CN1Challenges.+]

/-- The solution side: the proof. It imports Mathlib and, in `CN1/Assembly/Positivity.lean`,
`OAI.NumberTheory.DirichletL.Nonvanishing`. -/
@[default_target]
lean_lib CN1 where
  globs := #[`CN1.+]
