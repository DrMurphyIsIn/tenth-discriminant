import CN1.Epstein.Epstein
import CN1.ChowlaSelberg.Form

/-!
# Bridge to the Epstein sum `CS.Z (disc m)` of `CN1.ChowlaSelberg`

`CN1.ChowlaSelberg.Form` writes the principal form of the discriminant `d` as the real-valued
`CS.Q d x y = x² + (d % 2) x y + ((d + d % 2) / 4) y²` and the Epstein sum as
`CS.Z d s = Σ_{v ∈ ℤ²} (Q d v)^{-s}`. For `d = disc m` this is `CN1.Foundations.principalForm m`
(`principalForm_cast_eq_Q`), so the Epstein identity reads `ζ(s) L(s, χ_{-d}) = ½ Z_{disc m}(s)`
(`epstein_identity_Z`), the input to the Chowla–Selberg evaluation at `s = 7/8` (after the
continuation lemma of `CN1.ChowlaSelberg.Continuation`). This file is the only one in `CN1.Epstein`
that imports `CN1.ChowlaSelberg`.
-/

set_option autoImplicit false

namespace CN1.Epstein

open NumberField CN1.Foundations

variable {m : ℕ}

/-- `disc m ≡ 0 or 3 (mod 4)`. -/
theorem isDisc_disc (m : ℕ) : CS.IsDisc (disc m) := by
  unfold CS.IsDisc disc
  split_ifs with h3 <;> omega

/-- `3 ≤ disc m` for `m ≠ 0`. -/
theorem three_le_disc (hm0 : m ≠ 0) : 3 ≤ disc m := by
  unfold disc
  split_ifs with h3 <;> omega

/-- `CN1.Foundations.principalForm m` is `CN1.CS.Q (disc m)`. -/
theorem principalForm_cast_eq_Q (m : ℕ) (x y : ℤ) :
    ((principalForm m x y : ℤ) : ℝ) = CS.Q (disc m) x y := by
  unfold principalForm CS.Q CS.bq CS.cq disc
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have h2 : m % 2 = 1 := by omega
    have hc1 : (m + 1) / 4 = c := by omega
    have hc2 : (m + m % 2) / 4 = c := by omega
    rw [hc1, hc2, h2]
    push_cast
    ring
  · have h2 : 4 * m % 2 = 0 := by omega
    have hc : (4 * m + 4 * m % 2) / 4 = m := by omega
    rw [hc, h2]
    push_cast
    ring

/-- The lattice sum over `principalForm m` is `CN1.CS.Z (disc m)`. -/
theorem latticeSum_eq_Z (m : ℕ) (s : ℂ) :
    ∑' v : ℤ × ℤ, ((principalForm m v.1 v.2 : ℤ) : ℂ) ^ (-s) = CS.Z (disc m) s := by
  unfold CS.Z
  refine tsum_congr fun v => ?_
  rw [← Complex.ofReal_intCast, principalForm_cast_eq_Q]

variable {K : Type*} [Field K] [NumberField K] {α : K} (hα : α ^ 2 = -(m : K))
  (hK : Module.finrank ℚ K = 2) (hm : Squarefree m)

include hα hK hm in
/-- **The Epstein identity in the notation of `CN1.ChowlaSelberg`**: `ζ(s) L(s, χ_{-d}) = ½ Z_{d}(s)`,
`d = disc m`,
for `Re s > 1`, when `classNumber K = 1` and `m ∉ {1, 3}`. -/
theorem epstein_identity_Z [NeZero (disc m)] (hm1 : m ≠ 1) (hm3 : m ≠ 3) (h1 : classNumber K = 1)
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * DirichletCharacter.LFunction (kroneckerChar m) s = (1 / 2) * CS.Z (disc m) s := by
  rw [epstein_identity hα hK hm hm1 hm3 h1 hs, latticeSum_eq_Z]

include hα hK hm in
/-- **The hand-off to `CN1.ChowlaSelberg`** (the hypothesis `hZ` of `CS_seven_eighths_zeta_mul`): the
Epstein identity quantified over `s`, for `classNumber K = 1` and `m ∉ {1, 3}` (the factor `½` is `1/w`
with `w = 2`, which is why `m = 1, 3` are excluded; together with `isDisc_disc m` and
`three_le_disc hm.ne_zero`). -/
theorem epstein_hZ [NeZero (disc m)] (hm1 : m ≠ 1) (hm3 : m ≠ 3) (h1 : classNumber K = 1) :
    ∀ s : ℂ, 1 < s.re →
      riemannZeta s * DirichletCharacter.LFunction (kroneckerChar m) s = (1 / 2 : ℂ) * CS.Z (disc m) s :=
  fun _ hs => epstein_identity_Z hα hK hm hm1 hm3 h1 hs

include hα hK hm in
/-- `ζ_K(s) = ½ Z_{disc m}(s)` for `Re s > 1`, when `classNumber K = 1` and `m ∉ {1, 3}`. -/
theorem dedekindZeta_eq_half_Z (hm1 : m ≠ 1) (hm3 : m ≠ 3) (h1 : classNumber K = 1)
    {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s = (1 / 2) * CS.Z (disc m) s := by
  rw [dedekindZeta_eq_half_latticeSum hα hK hm hm1 hm3 h1 hs, latticeSum_eq_Z]

end CN1.Epstein
