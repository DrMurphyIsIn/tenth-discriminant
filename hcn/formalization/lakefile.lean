import Lake

open System Lake DSL

/-!
Lean project for the proof that the imaginary quadratic fields of class number at most two are
exactly the 9 of class number one and the 18 of class number two, without Heegner's method (no
j-invariant or singular moduli occur in the closure), linear forms in logarithms, or Gross–Zagier;
it does use the Jacobi theta function and, through OpenAI's proof, non-holomorphic Eisenstein series
(`HCN.classNumber_le_two_iff` and `HCN.classNumber_eq_two_iff` in `HCN/Main.lean`).

The one dependency is openai/math at the same pinned commit as the first proof in
`../../formalization/`. It brings Lean v4.34.1, Mathlib `d13f23b` and OpenAI's zero-free region
`Re s > 7/8` for Dirichlet L-functions; its Lean proof is inside the closure of both theorems.
Every other package in `lake-manifest.json` is a dependency of openai/math at the revision
openai/math pins, exactly as in `../../formalization/lake-manifest.json`.

openai/math ships Lean-v4.34.1 compatibility patches for 23 of those packages
(`lean/patches/*-lean4341.patch`). Its lakefile applies them only when openai/math is the root
project, not when it is a dependency, so here they are applied by `scripts/apply_oai_patches.sh`
(the same script as the first proof's), which must run once before the first `lake build`.
-/

package HCN where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require OAI from git
  "https://github.com/openai/math" @ "adc7f1241b42e322a6451854ab7e4b4c146bf78a" / "lean"

/-- The challenge side: the two statements with `sorry`, importing Mathlib only. -/
lean_lib HCNChallenges where
  globs := #[`HCNChallenges.+]

/-- The first proof's modules, vendored verbatim from `../../formalization/CN1/`. -/
lean_lib CN1 where
  globs := #[`CN1.+]

/-- The solution side: the new development. -/
@[default_target]
lean_lib HCN where
  globs := #[`HCN.+]

/-- Negative controls: the three tampered challenge statements, which Comparator must reject against
`HCN.Main`. Outside lean_lib HCN, and never imported by it. Never import a module of this library
together with `HCN.Main` (see README.md, "One rule"). -/
lean_lib HCNNegControls where
  globs := #[`HCNNegControls.+]
