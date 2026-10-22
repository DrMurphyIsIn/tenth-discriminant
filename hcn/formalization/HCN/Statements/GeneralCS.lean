import CN1.ChowlaSelberg.SevenEighths
import HCN.CS.Form
import HCN.CS.Slice
import HCN.CS.Remainder
import HCN.CS.MainTerm
import HCN.CS.Mono

/-!
# HCN.Statements.GeneralCS: the Chowla–Selberg formula for a general positive form

This file fixed the statements of the general Chowla–Selberg formula before their proofs were written; the proofs are
now in place. The specialisation lemmas at the end show
that at `(a, b, c) = (1, bq d, cq d)` the general objects ARE CN-1's `Z d`, `mainTerm d`, `E d`, so the general identity
specialises to CN-1's published `CN1.CS.CS_main` (`CS_main_principal`, proved from `CS_main_general`).

The form is `Q(x, y) = a x² + b x y + c y²` with real `a > 0` and `D = 4ac - b² > 0`, so
`Q = a (x + (b/2a) y)² + (D/4a) y²`. For `y ≠ 0`, Poisson summation in `x` gives the slice
`Σ_x Q(x,y)^{-s} = π^s/Γ(s) · a^{-1/2} Σ_k e^{2πik·by/(2a)} I(s; πDy²/(4a), πk²/a)`, with CN-1's kernel integral
`I(s; A, B) = ∫₀^∞ t^{s-3/2} e^{-At - B/t} dt` (`CN1.CS.I`). The `y = 0` slice is `2 a^{-s} ζ(2s)`; the `k = 0` terms give
`2 π^s a^{-1/2} Γ(s-1/2)/Γ(s) (4a/(πD))^{s-1/2} ζ(2s-1)`; the rest is `2 E_Q(s)`.

The remainder bound at `7/8` is the SHARP majorant `Rp = 2 Bg`, from `‖I‖ ≤ e^{-√(AB)} (2/A)^{σ-1/2}
Γ(σ-1/2)` (CN-1's `norm_I_le`), `√(AB) = c|k||y|` with `c = π√D/(2a)`, `(2/A)^{3/8} ≤ (8a/(πD))^{3/8}` and `|k||y| ≥ |k|+|y|-1`:
`Σ_{y≠0,k≠0} e^{-c|k||y|} ≤ 4e^{-c}/(1-e^{-c})²`. CN-1's own `B` uses the weaker split `|k||y| ≥ (|k|+|y|)/2`, giving
`e^{-c}/(1-e^{-c/2})²`; generalised to `a`, that weaker form only gives `h ≤ 2 ⇒ d ≤ 5248` (an mpmath computation),
whereas the sharp form gives `d ≤ 4777`. So `norm_Eg_seven_eighths_le` is a NEW lemma, not a pure refactor of
`norm_S_seven_eighths_le`. At `a = 1` the sharp bound is `≤ CN-1's B d` (`Bg_one_le_B`, proved here).
-/

set_option autoImplicit false

open Complex Set
open scoped Real

namespace HCN.CS

/-- The discriminant `D = 4ac - b²` of `a x² + b x y + c y²` (positive definite iff `a > 0` and `D > 0`). -/
noncomputable def disc (a b c : ℝ) : ℝ := 4 * a * c - b ^ 2

/-- The general form `Q(x, y) = a x² + b x y + c y²`, real-valued on `ℤ²`. -/
noncomputable def Qg (a b c : ℝ) (x y : ℤ) : ℝ := a * (x : ℝ) ^ 2 + b * x * y + c * (y : ℝ) ^ 2

/-- The Epstein zeta sum `Z_Q(s) = Σ′ Q(x, y)^{-s}` (the `p = 0` term is `0 ^ (-s) = 0` for `s ≠ 0`). -/
noncomputable def Zg (a b c : ℝ) (s : ℂ) : ℂ := ∑' p : ℤ × ℤ, (Qg a b c p.1 p.2 : ℂ) ^ (-s)

/-- The phase `e^{2πi k α}` with the theta shift `α = b y / (2a)`; a complex unit (CN-1's `sgn` at `a = 1`). -/
noncomputable def phase (a b : ℝ) (k y : ℤ) : ℂ :=
  cexp (2 * π * Complex.I * k * ((b * y / (2 * a) : ℝ) : ℂ))

/-- `A_y = π D y² / (4a)` (CN-1's `ay d y = π d y²/4` at `a = 1`, `D = d`). -/
noncomputable def ayg (a b c : ℝ) (y : ℤ) : ℝ := π * disc a b c * (y : ℝ) ^ 2 / (4 * a)

/-- `B_k = π k² / a` (CN-1's `bk k` at `a = 1`). -/
noncomputable def bkg (a : ℝ) (k : ℤ) : ℝ := π * (k : ℝ) ^ 2 / a

/-- The `(y, k)` remainder term `e^{2πik·by/(2a)} I(s; A_y, B_k)`, and `0` if `y = 0 ∨ k = 0`. -/
noncomputable def Rtermg (a b c : ℝ) (s : ℂ) (p : ℤ × ℤ) : ℂ :=
  if p.1 = 0 ∨ p.2 = 0 then 0 else phase a b p.2 p.1 * CN1.CS.I s (ayg a b c p.1) (bkg a p.2)

/-- `S_Q(s) = Σ_{y ≠ 0} Σ_{k ≠ 0} e^{2πik·by/(2a)} I(s; A_y, B_k)`, as a sum over `ℤ²`. -/
noncomputable def Sg (a b c : ℝ) (s : ℂ) : ℂ := ∑' p : ℤ × ℤ, Rtermg a b c s p

/-- The remainder `E_Q(s) = π^s/(2Γ(s)) · a^{-1/2} · S_Q(s)`. -/
noncomputable def Eg (a b c : ℝ) (s : ℂ) : ℂ :=
  (π : ℂ) ^ s * (Gamma s)⁻¹ / 2 * (((Real.sqrt a)⁻¹ : ℝ) : ℂ) * Sg a b c s

/-- The main term `a^{-s} ζ(2s) + π^s Γ(s-1/2) Γ(s)⁻¹ a^{-1/2} (4a/(πD))^{s-1/2} ζ(2s-1)`. -/
noncomputable def mainTermg (a b c : ℝ) (s : ℂ) : ℂ :=
  (a : ℂ) ^ (-s) * riemannZeta (2 * s) +
    (π : ℂ) ^ s * Gamma (s - 1 / 2) * (Gamma s)⁻¹ * (((Real.sqrt a)⁻¹ : ℝ) : ℂ) *
      ((4 * a / (π * disc a b c) : ℝ) : ℂ) ^ (s - 1 / 2) * riemannZeta (2 * s - 1)

/-- The exponent `c_Q = π √D / (2a)` in `e^{-c_Q |k| |y|}`. -/
noncomputable def cstg (a D : ℝ) : ℝ := π * Real.sqrt D / (2 * a)

/-- The sharp bound on `|E_Q(7/8)|` (`Rp = 2 Bg`):
`Bg(a, D) = 2 π^{7/8} Γ(3/8)/Γ(7/8) · a^{-1/2} · (8a/(πD))^{3/8} · e^{-c}/(1 - e^{-c})²`, `c = π√D/(2a)`. -/
noncomputable def Bg (a D : ℝ) : ℝ :=
  2 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * (Real.sqrt a)⁻¹ *
    (8 * a / (π * D)) ^ (3 / 8 : ℝ) * (Real.exp (-cstg a D) / (1 - Real.exp (-cstg a D)) ^ 2)

variable {a b c : ℝ} {s : ℂ}

/-! ### Proof glue

The interface objects above as instances of the generic helpers in `HCN.CS.*` (namespace `HCN.CSAux`): the slice of
`Qg` is `CSAux.slice_gen` with `A = a`, `α = by/(2a)`, `Y = ayg y`; `Rtermg` is `CSAux.T (phase a b) (ayg a b c) (bkg a)`
with `A_y = (πD/(4a)) y²`, `B_k = (π/a) k²`, so `√(αβ) = cstg a D` and `2/α = 8a/(πD)`. -/

namespace Glue

lemma ayg_eq (a b c : ℝ) (y : ℤ) : ayg a b c y = π * disc a b c / (4 * a) * (y : ℝ) ^ 2 := by
  unfold ayg; ring

lemma bkg_eq (a : ℝ) (k : ℤ) : bkg a k = π / a * (k : ℝ) ^ 2 := by
  unfold bkg; ring

lemma norm_phase (a b : ℝ) (k y : ℤ) : ‖phase a b k y‖ = 1 :=
  CSAux.norm_cexp_two_pi_I_mul k _

lemma conj_phase (a b : ℝ) (k y : ℤ) : (starRingEnd ℂ) (phase a b k y) = phase a b (-k) y := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast, Int.cast_neg]
  ring

lemma phase_zero (a b : ℝ) (y : ℤ) : phase a b 0 y = 1 := by
  simp [phase]

lemma Sg_eq (a b c : ℝ) (s : ℂ) :
    Sg a b c s = ∑' p : ℤ × ℤ, CSAux.T (phase a b) (ayg a b c) (bkg a) s p := rfl

lemma alpha_pos (ha : 0 < a) (hD : 0 < disc a b c) : 0 < π * disc a b c / (4 * a) := by
  positivity

lemma beta_pos (ha : 0 < a) : 0 < π / a := by
  positivity

lemma sqrt_alpha_beta (ha : 0 < a) (hD : 0 < disc a b c) :
    Real.sqrt (π * disc a b c / (4 * a) * (π / a)) = cstg a (disc a b c) := by
  unfold cstg
  rw [show π * disc a b c / (4 * a) * (π / a) = (π * Real.sqrt (disc a b c) / (2 * a)) ^ 2 by
    rw [div_pow, mul_pow, Real.sq_sqrt hD.le]; ring]
  exact Real.sqrt_sq (by positivity)

lemma two_div_alpha (ha : 0 < a) (hD : 0 < disc a b c) :
    2 / (π * disc a b c / (4 * a)) = 8 * a / (π * disc a b c) := by
  field_simp
  ring

lemma summable_Rtermg (ha : 0 < a) (hD : 0 < disc a b c) (hs : 1 / 2 < s.re) :
    Summable (Rtermg a b c s) :=
  CSAux.summable_T (norm_phase a b) (alpha_pos ha hD) (beta_pos ha) (ayg_eq a b c) (bkg_eq a) hs

/-- The general slice, `y ≠ 0`, with the `k = 0` term separated:
`Σ_x Q(x, y)^{-s} = π^s/Γ(s) · a^{-1/2} (I(s; A_y, 0) + Σ_k Rtermg(y, k))`. -/
lemma slice_split (ha : 0 < a) (hD : 0 < disc a b c) (hs : 1 < s.re) {y : ℤ} (hy : y ≠ 0) :
    ∑' x : ℤ, (Qg a b c x y : ℂ) ^ (-s) =
      (π : ℂ) ^ s / Gamma s * ((((Real.sqrt a)⁻¹ : ℝ) : ℂ) *
        (CN1.CS.I s (ayg a b c y) 0 + ∑' k : ℤ, Rtermg a b c s (y, k))) := by
  have hs' : 1 / 2 < s.re := by linarith
  have hY : 0 < ayg a b c y := by
    rw [ayg_eq]
    have : (y : ℝ) ≠ 0 := by exact_mod_cast hy
    have := alpha_pos ha hD
    positivity
  have h := CSAux.slice_gen (q := fun x : ℤ => Qg a b c x y) (Bk := bkg a) (α := b * y / (2 * a)) ha hY
    (fun x => CSAux.quad_eq ha (x : ℝ) (y : ℝ)) (fun k => rfl) hs
    (CSAux.summable_quad_rpow_slice ha hD hs y)
  rw [h]
  congr 2
  refine (CSAux.tsum_u_I_split (u := phase a b) (norm_phase a b) (alpha_pos ha hD) (beta_pos ha)
    (ayg_eq a b c) (bkg_eq a) hs' hy).trans ?_
  rw [phase_zero, one_mul]
  simp [bkg, Rtermg, CSAux.T]

end Glue

/-! ### The general Chowla–Selberg statements -/

/-- **Chowla–Selberg for a general positive form, on `re s > 1`:**
`½ Z_Q(s) = a^{-s} ζ(2s) + π^s Γ(s-1/2)/Γ(s) a^{-1/2} (4a/(πD))^{s-1/2} ζ(2s-1) + E_Q(s)`. -/
theorem CS_main_general (ha : 0 < a) (hD : 0 < disc a b c) (hs : 1 < s.re) :
    (1 / 2 : ℂ) * Zg a b c s = mainTermg a b c s + Eg a b c s := by
  have hs' : 1 / 2 < s.re := by linarith
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hα := Glue.alpha_pos ha hD
  have hZ : Zg a b c s = ∑' y : ℤ, ∑' x : ℤ, (Qg a b c x y : ℂ) ^ (-s) := by
    have hsum : Summable (fun p : ℤ × ℤ => (Qg a b c p.1 p.2 : ℂ) ^ (-s)) :=
      CSAux.summable_quad_cpow ha hD hs
    have e := (Equiv.prodComm ℤ ℤ).tsum_eq (fun p : ℤ × ℤ => (Qg a b c p.1 p.2 : ℂ) ^ (-s))
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] at e
    rw [Zg, ← e]
    exact hsum.prod_symm.tsum_prod' fun y => CSAux.summable_quad_cpow_slice ha hD hs y
  have hT : ∀ y : ℤ, ∑' x : ℤ, (Qg a b c x y : ℂ) ^ (-s) =
      (if y = 0 then (a : ℂ) ^ (-s) * (2 * riemannZeta (2 * s)) else 0) +
        (π : ℂ) ^ s / Gamma s * ((((Real.sqrt a)⁻¹ : ℝ) : ℂ) *
          ((if y = 0 then 0 else CN1.CS.I s (ayg a b c y) 0) + ∑' k : ℤ, Rtermg a b c s (y, k))) := by
    intro y
    by_cases hy : y = 0
    · subst hy
      simp only [if_true]
      have hQ0 : ∀ x : ℤ, (Qg a b c x 0 : ℂ) = ((a * (x : ℝ) ^ 2 : ℝ) : ℂ) := fun x => by simp [Qg]
      simp_rw [hQ0]
      rw [CSAux.tsum_a_sq_cpow ha hs']
      have h0 : ∀ k : ℤ, Rtermg a b c s (0, k) = 0 := fun k => by simp [Rtermg]
      simp [h0]
    · simp only [if_neg hy, zero_add]
      exact Glue.slice_split ha hD hs hy
  have hD0 : Summable fun y : ℤ => (if y = 0 then (a : ℂ) ^ (-s) * (2 * riemannZeta (2 * s)) else 0) :=
    (hasSum_ite_eq 0 _).summable
  have hI0 : ∀ y : ℤ, (if y = 0 then 0 else CN1.CS.I s (ayg a b c y) 0) =
      (if y = 0 then 0 else CN1.CS.I s (π * disc a b c / (4 * a) * (y : ℝ) ^ 2) 0) := fun y => by
    rw [Glue.ayg_eq]
  have hA : Summable fun y : ℤ => (if y = 0 then 0 else CN1.CS.I s (ayg a b c y) 0) := by
    simp_rw [hI0]
    exact CSAux.summable_I_zero_gen hα hs
  have hAsum : ∑' y : ℤ, (if y = 0 then 0 else CN1.CS.I s (ayg a b c y) 0) =
      Gamma (s - 1 / 2) * ((4 * a / (π * disc a b c) : ℝ) : ℂ) ^ (s - 1 / 2) *
        (2 * riemannZeta (2 * s - 1)) := by
    simp_rw [hI0]
    rw [CSAux.tsum_I_zero_gen hα hs, inv_div]
  have hRs := Glue.summable_Rtermg ha hD hs'
  have hR : Summable fun y : ℤ => ∑' k : ℤ, Rtermg a b c s (y, k) :=
    (hRs.hasSum.prod_fiberwise fun y => (hRs.prod_factor y).hasSum).summable
  have hS : Sg a b c s = ∑' y : ℤ, ∑' k : ℤ, Rtermg a b c s (y, k) :=
    CSAux.tsum_T_eq_tsum_tsum (Glue.norm_phase a b) hα (Glue.beta_pos ha) (Glue.ayg_eq a b c)
      (Glue.bkg_eq a) hs'
  rw [hZ]
  simp_rw [hT]
  rw [hD0.tsum_add (((hA.add hR).mul_left _).mul_left _), tsum_ite_eq 0 (fun _ => _), tsum_mul_left,
    tsum_mul_left, hA.tsum_add hR, hAsum, ← hS]
  unfold mainTermg Eg
  field_simp
  ring

/-- **Holomorphy** of the right side on `{re s > 1/2} \ {1}` (as CN-1's `differentiableOn_mainTerm_add_E`). -/
theorem differentiableOn_mainTermg_add_Eg (ha : 0 < a) (hD : 0 < disc a b c) :
    DifferentiableOn ℂ (fun s => mainTermg a b c s + Eg a b c s) ({s : ℂ | 1 / 2 < s.re} \ {1}) := by
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs
  simp only [mem_setOf_eq] at hs1
  have hs2' : s ≠ 1 := fun h => hs2 (mem_singleton_iff.mpr h)
  have hD' : 0 < 4 * a / (π * disc a b c) := by positivity
  apply DifferentiableAt.differentiableWithinAt
  have hz1 : DifferentiableAt ℂ (fun s => riemannZeta (2 * s)) s := by
    refine (differentiableAt_riemannZeta ?_).comp s (differentiableAt_id.const_mul 2)
    intro h
    have := congrArg re h
    simp at this
    linarith
  have hz2 : DifferentiableAt ℂ (fun s => riemannZeta (2 * s - 1)) s := by
    refine (differentiableAt_riemannZeta ?_).comp s ((differentiableAt_id.const_mul 2).sub_const 1)
    intro h
    exact hs2' (by linear_combination (1 / 2 : ℂ) * h)
  have hπ : DifferentiableAt ℂ (fun s : ℂ => (π : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr Real.pi_pos.ne'))
  have hav : DifferentiableAt ℂ (fun s : ℂ => (a : ℂ) ^ (-s)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr ha.ne'))
  have hΓ : DifferentiableAt ℂ (fun s : ℂ => Gamma (s - 1 / 2)) s := by
    refine (differentiableAt_Gamma _ ?_).comp s (differentiableAt_id.sub_const _)
    intro m h
    have := congrArg re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hΓi : DifferentiableAt ℂ (fun s : ℂ => (Gamma s)⁻¹) s :=
    Complex.differentiable_one_div_Gamma s
  have h4 : DifferentiableAt ℂ (fun s : ℂ => ((4 * a / (π * disc a b c) : ℝ) : ℂ) ^ (s - 1 / 2)) s :=
    (differentiableAt_id.sub_const _).const_cpow (Or.inl (ofReal_ne_zero.mpr hD'.ne'))
  have hS : DifferentiableAt ℂ (Sg a b c) s :=
    (CSAux.differentiableOn_tsum_T (Glue.norm_phase a b) (Glue.alpha_pos ha hD) (Glue.beta_pos ha)
      (Glue.ayg_eq a b c) (Glue.bkg_eq a) s hs1).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hs1)
  have hm : DifferentiableAt ℂ (mainTermg a b c) s :=
    (hav.mul hz1).add (((((hπ.mul hΓ).mul hΓi).mul_const _).mul h4).mul hz2)
  have hE : DifferentiableAt ℂ (Eg a b c) s :=
    (((hπ.mul hΓi).div_const 2).mul_const _).mul hS
  exact hm.add hE

/-- **The main term at `s = 7/8`**, with real coefficients:
`a^{-7/8} ζ(7/4) + π^{7/8} Γ(3/8)/Γ(7/8) a^{-1/2} (4a/(πD))^{3/8} · ζ(3/4)`. -/
theorem mainTermg_seven_eighths (ha : 0 < a) (hD : 0 < disc a b c) :
    mainTermg a b c (7 / 8) =
      ((a ^ (-(7 / 8 : ℝ)) : ℝ) : ℂ) * riemannZeta (7 / 4) +
        ((π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) * (Real.sqrt a)⁻¹ *
          (4 * a / (π * disc a b c)) ^ (3 / 8 : ℝ) : ℝ) : ℂ) * riemannZeta (3 / 4) := by
  unfold mainTermg
  have h1 : (2 : ℂ) * (7 / 8) = 7 / 4 := by norm_num
  have h2 : (2 : ℂ) * (7 / 8) - 1 = 3 / 4 := by norm_num
  have h3 : (7 / 8 : ℂ) - 1 / 2 = ((3 / 8 : ℝ) : ℂ) := by push_cast; norm_num
  have hn : -(7 / 8 : ℂ) = ((-(7 / 8) : ℝ) : ℂ) := by push_cast; ring
  have h0 : (7 / 8 : ℂ) = ((7 / 8 : ℝ) : ℂ) := by push_cast; ring
  have hD' : 0 ≤ 4 * a / (π * disc a b c) := by positivity
  rw [h2, h1, h3, hn, h0, ← Complex.ofReal_cpow ha.le, ← Complex.ofReal_cpow Real.pi_pos.le,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_cpow hD']
  push_cast
  ring

/-- **`E_Q(7/8)` is real.** -/
theorem Eg_seven_eighths_im (ha : 0 < a) (hD : 0 < disc a b c) : (Eg a b c (7 / 8)).im = 0 := by
  have h0 : (7 / 8 : ℂ) = ((7 / 8 : ℝ) : ℂ) := by push_cast; ring
  have hS : (Sg a b c ((7 / 8 : ℝ) : ℂ)).im = 0 :=
    CSAux.tsum_T_ofReal_im (Glue.conj_phase a b) (fun k => by simp [bkg]) (7 / 8)
  have hS' : (Sg a b c (7 / 8)).im = 0 := by rw [h0]; exact hS
  rw [h0, Eg, ← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal]
  rw [show ((π ^ (7 / 8 : ℝ) : ℝ) : ℂ) * ((Real.Gamma (7 / 8) : ℝ) : ℂ)⁻¹ / 2 * (((Real.sqrt a)⁻¹ : ℝ) : ℂ) =
      ((π ^ (7 / 8 : ℝ) * (Real.Gamma (7 / 8))⁻¹ / 2 * (Real.sqrt a)⁻¹ : ℝ) : ℂ) by push_cast; ring]
  simp [Complex.mul_im, hS']

/-- **The sharp remainder bound at `7/8`:** `‖E_Q(7/8)‖ ≤ Bg(a, D)`. -/
theorem norm_Eg_seven_eighths_le (ha : 0 < a) (hD : 0 < disc a b c) :
    ‖Eg a b c (7 / 8)‖ ≤ Bg a (disc a b c) := by
  have hs : 1 / 2 < (7 / 8 : ℂ).re := by norm_num
  have hre : (7 / 8 : ℂ).re - 1 / 2 = 3 / 8 := by norm_num
  have hSb := CSAux.norm_tsum_T_le (Glue.norm_phase a b) (Glue.alpha_pos ha hD) (Glue.beta_pos ha)
    (Glue.ayg_eq a b c) (Glue.bkg_eq a) hs
  rw [hre, Glue.two_div_alpha ha hD, Glue.sqrt_alpha_beta ha hD, ← Glue.Sg_eq] at hSb
  have hπ : ‖(π : ℂ) ^ (7 / 8 : ℂ)‖ = π ^ (7 / 8 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    norm_num
  have hG : Gamma (7 / 8 : ℂ) = (Real.Gamma (7 / 8) : ℂ) := by
    rw [← Complex.Gamma_ofReal]
    congr 1
    push_cast
    ring
  have hGpos : 0 < Real.Gamma (7 / 8) := Real.Gamma_pos_of_pos (by norm_num)
  have hC : ‖((((Real.sqrt a)⁻¹ : ℝ) : ℂ))‖ = (Real.sqrt a)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [Eg, norm_mul, norm_mul, norm_div, norm_mul, hπ, hG, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hGpos, hC, h2]
  have hK : 0 ≤ π ^ (7 / 8 : ℝ) * (Real.Gamma (7 / 8))⁻¹ / 2 * (Real.sqrt a)⁻¹ := by positivity
  calc π ^ (7 / 8 : ℝ) * (Real.Gamma (7 / 8))⁻¹ / 2 * (Real.sqrt a)⁻¹ * ‖Sg a b c (7 / 8)‖
      ≤ π ^ (7 / 8 : ℝ) * (Real.Gamma (7 / 8))⁻¹ / 2 * (Real.sqrt a)⁻¹ *
          (Real.Gamma (3 / 8) * (8 * a / (π * disc a b c)) ^ (3 / 8 : ℝ) *
            (4 * (Real.exp (-cstg a (disc a b c)) / (1 - Real.exp (-cstg a (disc a b c))) ^ 2))) :=
        mul_le_mul_of_nonneg_left hSb hK
    _ = Bg a (disc a b c) := by
        unfold Bg
        field_simp
        ring

/-- **The a-monotonicity lemma**: `Bg(·, D)` is increasing on `(0, (2/3)√D]`,
since `d/da log Bg > 0 ⟺ c (1 + 2e^{-c}/(1 - e^{-c})) > 1/8`, and `c = π√D/(2a) ≥ 3π/4` there. (What is formalised is
the weaker side condition `c ≥ 1/8` at the larger point, `HCN.CSAux.one_eighth_le_cst`.) -/
theorem Bg_mono {a' D : ℝ} (hD : 0 < D) (ha : 0 < a) (haa' : a ≤ a') (ha' : a' ≤ 2 / 3 * Real.sqrt D) :
    Bg a D ≤ Bg a' D := by
  have ha'0 : 0 < a' := lt_of_lt_of_le ha haa'
  have hcore := CSAux.bg_core_mono hD ha haa' (CSAux.one_eighth_le_cst ha'0 ha')
  have hK : 0 ≤ 2 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 8)
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 7 / 8)
    positivity
  have e : ∀ x : ℝ, Bg x D = 2 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) *
      ((Real.sqrt x)⁻¹ * (8 * x / (π * D)) ^ (3 / 8 : ℝ) *
        (Real.exp (-(π * Real.sqrt D / (2 * x))) / (1 - Real.exp (-(π * Real.sqrt D / (2 * x)))) ^ 2)) := by
    intro x
    unfold Bg cstg
    ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_left hcore hK

/-! ### Consequences proved here from the statements above (no further `sorry`) -/

/-- **Continuation to `s = 7/8`** (as CN-1's `CS_seven_eighths`): if `F` is holomorphic on `{re s > 1/2} \ {1}` and
equals `½ Z_Q` on `re s > 1`, then `F(7/8) = mainTermg(7/8) + E_Q(7/8)`. -/
theorem CS_seven_eighths_general (ha : 0 < a) (hD : 0 < disc a b c) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F ({s : ℂ | 1 / 2 < s.re} \ {1}))
    (hZ : ∀ s : ℂ, 1 < s.re → F s = (1 / 2 : ℂ) * Zg a b c s) :
    F (7 / 8) = mainTermg a b c (7 / 8) + Eg a b c (7 / 8) := by
  have h := CN1.CS.eq_at_ofReal_of_differentiableOn_sdiff (a := 1 / 2) (x := 7 / 8) (by norm_num)
    (by norm_num) hF (differentiableOn_mainTermg_add_Eg ha hD)
    (fun s hs => by rw [hZ s hs, CS_main_general ha hD hs])
  have h78 : ((7 / 8 : ℝ) : ℂ) = (7 / 8 : ℂ) := by push_cast; ring
  rwa [h78] at h

/-! ### Specialisation to CN-1's principal form (proved here) -/

section Principal

open CN1.CS

variable {d : ℕ}

theorem disc_principal (hd : IsDisc d) : disc 1 (bq d) (cq d) = d := by
  have h1 : (4 * cq d : ℝ) = d + bq d := by exact_mod_cast four_mul_cq hd
  have h2 : (bq d : ℝ) ^ 2 = bq d := by exact_mod_cast bq_sq d
  unfold disc
  linarith

theorem Qg_principal (d : ℕ) (x y : ℤ) : Qg 1 (bq d) (cq d) x y = Q d x y := by
  simp [Qg, Q]

theorem Zg_principal (d : ℕ) (s : ℂ) : Zg 1 (bq d) (cq d) s = Z d s := by
  simp only [Zg, Z, Qg_principal]

theorem mainTermg_principal (hd : IsDisc d) (s : ℂ) :
    mainTermg 1 (bq d) (cq d) s = mainTerm d s := by
  simp only [mainTermg, mainTerm, disc_principal hd, Real.sqrt_one, inv_one, Complex.ofReal_one,
    Complex.one_cpow, one_mul, mul_one]

theorem phase_principal (d : ℕ) (k y : ℤ) : phase 1 (bq d) k y = sgn d k y := by
  rw [← exp_eq_sgn, phase, mul_one]

theorem Rtermg_principal (hd : IsDisc d) (s : ℂ) (p : ℤ × ℤ) :
    Rtermg 1 (bq d) (cq d) s p = Rterm d s p := by
  have hay : ayg 1 (bq d) (cq d) p.1 = ay d p.1 := by
    simp only [ayg, ay, disc_principal hd, mul_one]
  have hbk : bkg 1 p.2 = bk p.2 := by simp [bkg, bk]
  simp only [Rtermg, Rterm, phase_principal, hay, hbk]

theorem Eg_principal (hd : IsDisc d) (s : ℂ) : Eg 1 (bq d) (cq d) s = E d s := by
  have hS : Sg 1 (bq d) (cq d) s = S d s := by
    simp only [Sg, S, Rtermg_principal hd]
  simp only [Eg, E, hS, Real.sqrt_one, inv_one, Complex.ofReal_one, mul_one]

/-- **The regression:** `CS_main_general` at `(1, bq d, cq d)` is exactly CN-1's `CN1.CS.CS_main`. -/
theorem CS_main_principal (hd : IsDisc d) (h3 : 3 ≤ d) (hs : 1 < s.re) :
    (1 / 2 : ℂ) * Z d s = mainTerm d s + E d s := by
  have hD : 0 < disc 1 (bq d) (cq d) := by
    rw [disc_principal hd]; exact_mod_cast (by omega : 0 < d)
  rw [← Zg_principal, ← mainTermg_principal hd, ← Eg_principal hd]
  exact CS_main_general one_pos hD hs

/-- At `a = 1` the sharp bound is at most CN-1's `B d`: `cstg 1 d = cst d` and `(1 - e^{-c/2})² ≤ (1 - e^{-c})²`.
So `norm_Eg_seven_eighths_le` at `(1, bq d, cq d)` implies CN-1's `norm_E_seven_eighths_le`. -/
theorem Bg_one_le_B (h3 : 3 ≤ d) : Bg 1 d ≤ B d := by
  have hc : cstg 1 d = cst d := by simp [cstg, cst]
  have hcpos : 0 < cst d := cst_pos (by omega)
  have e1 : Real.exp (-cst d) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have e2 : Real.exp (-(cst d / 2)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have e3 : Real.exp (-cst d) ≤ Real.exp (-(cst d / 2)) := Real.exp_le_exp.mpr (by linarith)
  have hden : (1 - Real.exp (-(cst d / 2))) ^ 2 ≤ (1 - Real.exp (-cst d)) ^ 2 := by
    have : 0 < 1 - Real.exp (-(cst d / 2)) := by linarith
    nlinarith
  have hpre : 0 ≤ 2 * π ^ (7 / 8 : ℝ) * Real.Gamma (3 / 8) / Real.Gamma (7 / 8) *
      (8 / (π * d)) ^ (3 / 8 : ℝ) := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 8)
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 7 / 8)
    positivity
  have hfrac : Real.exp (-cst d) / (1 - Real.exp (-cst d)) ^ 2 ≤
      Real.exp (-cst d) / (1 - Real.exp (-(cst d / 2))) ^ 2 := by
    apply div_le_div_of_nonneg_left (Real.exp_pos _).le
    · have : 0 < 1 - Real.exp (-(cst d / 2)) := by linarith
      positivity
    · exact hden
  unfold Bg B
  rw [hc, Real.sqrt_one, inv_one, mul_one, mul_one]
  exact mul_le_mul_of_nonneg_left hfrac hpre

end Principal

end HCN.CS
