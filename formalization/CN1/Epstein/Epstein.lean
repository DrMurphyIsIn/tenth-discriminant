import CN1.Epstein.Lattice
import CN1.Epstein.Factorization

/-!
# The Epstein identity (steps 1–2 of the argument), assembled

Pinned environment: Lean v4.34.1, Mathlib d13f23b. Imports: Mathlib and `CN1.Foundations` only.

For the statement's `K` (`finrank 2`, `α² = -m`, `m` squarefree) with `χ = kroneckerChar m`
(level `d = disc m`) and `Q = principalForm m`:

* `dedekindZeta_eq_riemannZeta_mul_LFunction` (step 2, any `m`):
  `ζ_K(s) = ζ(s) · L(s, χ_{-d})` for `Re s > 1`;
* `dedekindZeta_eq_half_latticeSum` (step 1, `m ∉ {1, 3}`, `h_K = 1`):
  `ζ_K(s) = ½ Σ_{(x,y) ∈ ℤ²} Q(x,y)^{-s}` for `Re s > 1` (the `(0,0)` term is `0 ^ (-s) = 0`);
* `epstein_identity`: the two combined, `ζ(s) L(s, χ_{-d}) = ½ Σ′ Q^{-s}`, which is the input to
  the Chowla–Selberg evaluation of `CN1.ChowlaSelberg` (the bridge to its `CS.Z (disc m)` is in
  `Bridge.lean`).
-/

set_option autoImplicit false

namespace CN1.Epstein

open NumberField CN1.Foundations

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
  (hK : Module.finrank ℚ K = 2) (hm : Squarefree m)

include hα hK hm in
/-- **The Epstein identity.** If `classNumber K = 1` and `m ∉ {1, 3}`, then for `Re s > 1`
`ζ(s) · L(s, χ_{-d}) = ½ Σ_{(x,y) ∈ ℤ²} Q(x,y)^{-s}` (the `(0,0)` term is `0 ^ (-s) = 0`). -/
theorem epstein_identity [NeZero (disc m)] (hm1 : m ≠ 1) (hm3 : m ≠ 3) (h1 : classNumber K = 1)
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * DirichletCharacter.LFunction (kroneckerChar m) s =
      (1 / 2) * ∑' v : ℤ × ℤ, ((principalForm m v.1 v.2 : ℤ) : ℂ) ^ (-s) := by
  rw [← dedekindZeta_eq_riemannZeta_mul_LFunction hα hK hm hs,
    dedekindZeta_eq_half_latticeSum hα hK hm hm1 hm3 h1 hs]

include hα hK hm in
/-- The same with the primed sum written over `ℤ² ∖ {0}`. -/
theorem epstein_identity' [NeZero (disc m)] (hm1 : m ≠ 1) (hm3 : m ≠ 3) (h1 : classNumber K = 1)
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * DirichletCharacter.LFunction (kroneckerChar m) s =
      (1 / 2) * ∑' v : {v : ℤ × ℤ // v ≠ 0}, ((principalForm m v.1.1 v.1.2 : ℤ) : ℂ) ^ (-s) := by
  rw [epstein_identity hα hK hm hm1 hm3 h1 hs]
  congr 1
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr fun h => by rw [h, Complex.zero_re] at hs; linarith
  have h0 : ((principalForm m (0 : ℤ × ℤ).1 (0 : ℤ × ℤ).2 : ℤ) : ℂ) ^ (-s) = 0 := by
    simp [principalForm, Complex.zero_cpow hs0]
  symm
  exact tsum_subtype_eq_of_support_subset (s := {v : ℤ × ℤ | v ≠ 0})
    (f := fun v : ℤ × ℤ => ((principalForm m v.1 v.2 : ℤ) : ℂ) ^ (-s)) fun v hv => by
      rintro rfl
      exact (Function.mem_support.mp hv) h0

end CN1.Epstein
