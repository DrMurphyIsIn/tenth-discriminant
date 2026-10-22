import CN1.ChowlaSelberg.MainTerm
import CN1.ChowlaSelberg.Continuation

/-!
# CN1.ChowlaSelberg.SevenEighths: the Chowla–Selberg identity at `s = 7/8` (step 3 of the argument)

Given any `F` holomorphic on `{re s > 1/2} \ {1}` with `F s = ½ Z_Q(s)` for `re s > 1` (the
Epstein identity of `CN1.Epstein` supplies `F = ζ · L(·, χ_{-d})`), the identity theorem on the
convex region `V (1/2) (7/8)` (`Continuation.lean`) continues `F = mainTerm + E_d` from `re s > 1`
to `s = 7/8`:

  `F(7/8) = ζ(7/4) + π^{7/8} Γ(3/8)/Γ(7/8) (4/(πd))^{3/8} ζ(3/4) + E_d(7/8)`,

with `E_d(7/8)` real and `|E_d(7/8)| ≤ B(d) ≤ B₀(d) ≤ B₁(d)` (`Remainder.lean`). Everything numerical
is stated about Mathlib's `riemannZeta`, `Real.Gamma`, `Real.pi`, `Real.exp`, `Real.sqrt` and
`Real.rpow` (so that the trust base stays Mathlib's), and the remainder is this file's `E`, not a
separately defined function.
-/

open Complex Set
open scoped Real

namespace CN1.CS

variable {d : ℕ}

/-- `mainTerm d + E d` is holomorphic on `{re s > 1/2} \ {1}`. -/
theorem differentiableOn_mainTerm_add_E (h3 : 3 ≤ d) :
    DifferentiableOn ℂ (fun s => mainTerm d s + E d s) ({s : ℂ | 1 / 2 < s.re} \ {1}) :=
  (differentiableOn_mainTerm (by omega)).add ((differentiableOn_E h3).mono diff_subset)

/-- **Continuation to `s = 7/8`.** If `F` is holomorphic on `{re s > 1/2} \ {1}` and equals
`½ Z_Q` on `re s > 1`, then `F(7/8) = mainTerm d (7/8) + E_d(7/8)`. -/
theorem CS_seven_eighths (hd : IsDisc d) (h3 : 3 ≤ d) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F ({s : ℂ | 1 / 2 < s.re} \ {1}))
    (hZ : ∀ s : ℂ, 1 < s.re → F s = (1 / 2 : ℂ) * Z d s) :
    F (7 / 8) = mainTerm d (7 / 8) + E d (7 / 8) := by
  have h := eq_at_ofReal_of_differentiableOn_sdiff (a := 1 / 2) (x := 7 / 8) (by norm_num)
    (by norm_num) hF (differentiableOn_mainTerm_add_E h3)
    (fun s hs => by rw [hZ s hs, CS_main hd h3 hs])
  have h78 : ((7 / 8 : ℝ) : ℂ) = (7 / 8 : ℂ) := by push_cast; ring
  rwa [h78] at h

/-- The same, with the main term written out:
`F(7/8) = ζ(7/4) + π^{7/8} Γ(3/8)/Γ(7/8) (4/(πd))^{3/8} · ζ(3/4) + E_d(7/8)`. -/
theorem CS_seven_eighths_explicit (hd : IsDisc d) (h3 : 3 ≤ d) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F ({s : ℂ | 1 / 2 < s.re} \ {1}))
    (hZ : ∀ s : ℂ, 1 < s.re → F s = (1 / 2 : ℂ) * Z d s) :
    F (7 / 8) = riemannZeta (7 / 4) +
      ((π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) *
        (4 / (π * d)) ^ (3 / 8 : ℝ) : ℝ) : ℂ) * riemannZeta (3 / 4) + E d (7 / 8) := by
  rw [CS_seven_eighths hd h3 hF hZ, mainTerm_seven_eighths]

/-- The form for `F = ζ · L`: `L` holomorphic on `re s > 1/2` (e.g. an entire Dirichlet
`L`-function), and `ζ(s) L(s) = ½ Z_Q(s)` on `re s > 1`. -/
theorem CS_seven_eighths_zeta_mul (hd : IsDisc d) (h3 : 3 ≤ d) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 / 2 < s.re})
    (hZ : ∀ s : ℂ, 1 < s.re → riemannZeta s * L s = (1 / 2 : ℂ) * Z d s) :
    riemannZeta (7 / 8) * L (7 / 8) = riemannZeta (7 / 4) +
      ((π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) *
        (4 / (π * d)) ^ (3 / 8 : ℝ) : ℝ) : ℂ) * riemannZeta (3 / 4) + E d (7 / 8) := by
  have hF : DifferentiableOn ℂ (fun s => riemannZeta s * L s) ({s : ℂ | 1 / 2 < s.re} \ {1}) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => hs.2 (mem_singleton_iff.mpr h)
    exact (differentiableAt_riemannZeta hs1).differentiableWithinAt.mul ((hL.mono diff_subset) s hs)
  exact CS_seven_eighths_explicit hd h3 hF hZ

/-! ### The remainder at `7/8`, restated for `CN1.Numerics` -/

/-- `E_d(7/8)` is real. -/
theorem E_seven_eighths_im_eq_zero : (E d (7 / 8)).im = 0 := E_seven_eighths_im

/-- `|re E_d(7/8)| ≤ B(d)`. -/
theorem abs_E_seven_eighths_re_le (h3 : 3 ≤ d) : |(E d (7 / 8)).re| ≤ B d :=
  (Complex.abs_re_le_norm _).trans (norm_E_seven_eighths_le h3)

/-- `|re E_d(7/8)| ≤ B₀(d)` for `d ≥ 7`. -/
theorem abs_E_seven_eighths_re_le_B0 (h7 : 7 ≤ d) : |(E d (7 / 8)).re| ≤ B0 d :=
  (abs_E_seven_eighths_re_le (by omega)).trans (B_le_B0 h7)

/-- `|re E_d(7/8)| ≤ B₁(d) = 4 π^{7/8} Γ(3/8)/Γ(7/8) e^{-π√d/2}` for `d ≥ 7`. -/
theorem abs_E_seven_eighths_re_le_B1 (h7 : 7 ≤ d) : |(E d (7 / 8)).re| ≤ B1 d :=
  (abs_E_seven_eighths_re_le_B0 h7).trans (B0_le_B1 (by omega))

/-- `E_d(7/8)` as a real number: `E d (7/8) = ((E d (7/8)).re : ℂ)`. -/
theorem E_seven_eighths_eq_ofReal_re : E d (7 / 8) = ((E d (7 / 8)).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [E_seven_eighths_im_eq_zero]

end CN1.CS
