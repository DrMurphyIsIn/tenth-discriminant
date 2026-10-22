import Lake

open System Lake DSL

/-!
Lean project for the determinant proof of the class number one theorem for imaginary quadratic
fields (`CN1.classNumber_eq_one_iff` in `ELEM/Main.lean`), with no L-function, no zeta function and
no zero-free theorem in its closure.

The one dependency is Mathlib, required directly at the revision `d13f23b` (Lean v4.34.1), the same
Mathlib as the first proof in `../../formalization/`. Every other package in `lake-manifest.json` is
a dependency of Mathlib at the revision Mathlib pins. Unlike the first proof, nothing here needs
openai/math or any patch.
-/

package ELEM where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

/-- The challenge side: `CN1.classNumber_eq_one_iff` with `sorry`, copied unchanged from the first
proof (`formalization/CN1Challenges/ClassNumberOne.lean`). -/
lean_lib CN1Challenges where
  globs := #[`CN1Challenges.ClassNumberOne]

/-- Vendored verbatim from the first proof: the Mathlib-only foundations and the finite part. No
other module of the first proof is present. -/
lean_lib CN1 where
  globs := #[`CN1.Foundations.+, `CN1.Finite.+]

/-- The new development, one module per step of the argument. -/
@[default_target]
lean_lib ELEM where
  globs := #[`ELEM.+]

/-- Negative controls: the two tampered challenge statements, which Comparator must reject against
`ELEM.Main`. Outside lean_lib ELEM, and never imported by it. Never import a module of this library
together with `ELEM.Main` (see README.md, "One rule"). -/
lean_lib ELEMNegControls where
  globs := #[`ELEMNegControls.+]
