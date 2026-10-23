import CN1.Finite.Bridge
import CN1.Numerics.Glue
import CN1.Assembly.Positivity

/-!
# Assembly of the class number one theorem, conditional on the Epstein identity

Pinned environment: Lean v4.34.1, Mathlib d13f23b (the openai/math 7/8 environment).

This file assembles the six steps of the argument (listed in `CN1.Main`) into the statement of the
Comparator challenge `CN1Challenges.ClassNumberOne`, with the Epstein identity (steps 1–2) taken as
an explicit hypothesis, `EpsteinIdentity m`:

  `ζ(s) · L(s, χ_{-d}) = ½ · Z_d(s)` for `Re s > 1`, `d = disc m`, `χ_{-d} = kroneckerChar m`,
  `Z_d` the Epstein sum over the principal form (`CN1.CS.Z`, from `CN1.ChowlaSelberg.Form`).

`CN1.Main` discharges it with `CN1.Epstein.epstein_identity_Z`. The inputs, by module:

* `CN1.Foundations`: `disc`, `kroneckerChar`, `kroneckerChar_isQuadratic`, `kroneckerChar_ne_one`;
* `CN1.Finite.Bridge`: `classNumber_ne_one_of_foundations` (the finite part, `d ≤ 652`) and
  `classNumber_eq_one_of_foundations` (the converse for the nine);
* `CN1.Numerics.Glue` (on top of `CN1.ChowlaSelberg`): `disc_le_652_of_CS`, the analytic contradiction
  (Chowla–Selberg at `7/8`, the remainder bound, the certified numerics);
* `CN1.Assembly.Positivity`: `LFunction_seven_eighths_nonneg_of_isQuadratic`,
  which uses openai/math's zero-free region `Re s > 7/8` for Dirichlet L-functions;
* Mathlib: `DirichletCharacter.differentiable_LFunction` (`χ ≠ 1`).
-/

set_option autoImplicit false

open NumberField CN1.Foundations

namespace CN1.Assembly

variable {m : ℕ}

/-- `disc m ≠ 0` for `m ≠ 0`. -/
theorem disc_ne_zero (hm0 : m ≠ 0) : disc m ≠ 0 := by
  unfold disc; split_ifs <;> omega

/-- `disc m ≡ 0 or 3 (mod 4)`: `CN1.CS.IsDisc`. -/
theorem isDisc_disc (m : ℕ) : CS.IsDisc (disc m) := by
  unfold CS.IsDisc disc; split_ifs <;> omega

/-- `7 ≤ disc m` once `m ∉ {0, 1, 3}` (the three radicands with `d < 7` are `m = 3, 1` and the
excluded `m = 0`; `m = 2` has `d = 8`). -/
theorem seven_le_disc (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hm3 : m ≠ 3) : 7 ≤ disc m := by
  unfold disc; split_ifs <;> omega

/-- **The Epstein identity, in the notation of `CN1.ChowlaSelberg`**, as a proposition about the
radicand `m`:
`ζ(s) · L(s, χ_{-d}) = ½ Z_d(s)` on `Re s > 1`, with `d = disc m`. -/
def EpsteinIdentity (m : ℕ) [NeZero (disc m)] : Prop :=
  ∀ s : ℂ, 1 < s.re →
    riemannZeta s * DirichletCharacter.LFunction (kroneckerChar m) s = (1 / 2 : ℂ) * CS.Z (disc m) s

/-- **The analytic bound (steps 3–5 of the argument).** If the Epstein identity holds for `m` (squarefree,
`m ∉ {1, 3}`), then `disc m ≤ 652`. The field `K` enters only through the identity. -/
theorem disc_le_652_of_epstein [NeZero (disc m)] (hm : Squarefree m) (hm1 : m ≠ 1) (hm3 : m ≠ 3)
    (hE : EpsteinIdentity m) : disc m ≤ 652 := by
  have hχ1 : kroneckerChar m ≠ 1 := kroneckerChar_ne_one hm
  have hpos := CN1.LFunction_seven_eighths_nonneg_of_isQuadratic (kroneckerChar m)
    (kroneckerChar_isQuadratic m) hχ1
  exact Numerics.disc_le_652_of_CS (disc m) (isDisc_disc m) (seven_le_disc hm.ne_zero hm1 hm3)
    (L := DirichletCharacter.LFunction (kroneckerChar m))
    (DirichletCharacter.differentiable_LFunction hχ1).differentiableOn hE hpos.1 hpos.2

/-- **The class number one theorem, conditional on the Epstein identity.** This is the statement of
the Comparator challenge `CN1Challenges.ClassNumberOne` with one extra hypothesis `hE`: whenever
`classNumber K = 1` and `m ∉ {1, 3}`, the Epstein identity holds for `m`. `CN1.Main` supplies `hE`
from `CN1.Epstein.epstein_identity_Z`. -/
theorem classNumber_eq_one_iff_of_epstein (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K))
    (hE : ∀ [NeZero (disc m)], classNumber K = 1 → m ≠ 1 → m ≠ 3 → EpsteinIdentity m) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ) := by
  haveI : NeZero (disc m) := ⟨disc_ne_zero hm.ne_zero⟩
  refine ⟨fun h1 => ?_, Finite.classNumber_eq_one_of_foundations hK hm hsq⟩
  by_contra hnine
  have hm1 : m ≠ 1 := fun h => hnine (by simp [h])
  have hm3 : m ≠ 3 := fun h => hnine (by simp [h])
  -- the analytic bound `d ≤ 652` (steps 1–5), then the finite part (step 6)
  have hd : disc m ≤ 652 := disc_le_652_of_epstein hm hm1 hm3 (hE h1 hm1 hm3)
  exact Finite.classNumber_ne_one_of_foundations hK hm hsq hd hnine h1

end CN1.Assembly
