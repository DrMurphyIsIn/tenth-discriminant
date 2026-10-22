import Mathlib

/-!
# CN1.ChowlaSelberg.Continuation: a generic identity-theorem lemma

Two functions holomorphic on a region of the half-plane `{s | a < re s}` that avoids the pole
`s = 1`, which agree on `{s | 1 < re s}`, agree at every real point `x ∈ (a, 1)`.

The region is the explicit convex open set `V a x` below: the half-plane `a < re s`, a tilted
half-plane through the real axis between `x` and `1`, and the strip `|im s| < 1`. It contains `x`,
it does not contain `1`, and it contains a neighbourhood of the seed `s₀ = (3 - x)/2 + (3/4) i`,
which lies in `{s | 1 < re s}`. Convex sets are preconnected, so Mathlib's identity principle
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` applies, with no need to prove that a
punctured half-plane is connected (the pinned Mathlib has that only for a whole space minus a
point).

Intended uses: the Chowla–Selberg identity at `s = 7/8` (module `SevenEighths`), and real-valued
representations of `riemannZeta` at `3/4` and `7/8` (`CN1.Numerics`). Everything here is
Mathlib-only.
-/

open Complex Set

namespace CN1.CS

variable {a x : ℝ}

/-- The slope parameter `κ = 1 / (2 (1 - x))` of the tilted half-plane. -/
noncomputable def kappa (x : ℝ) : ℝ := (2 * (1 - x))⁻¹

/-- The tilted open half-plane `{s | κ re s - im s < κ x + 1/4}`: it contains `x` (as `0 < 1/4`)
and not `1` (as `κ (1 - x) = 1/2 > 1/4`). -/
def tilt (x : ℝ) : Set ℂ := {s | s.re * kappa x - s.im < x * kappa x + 1 / 4}

/-- The convex open region used for continuation: `a < re s`, the tilt, and `|im s| < 1`. -/
def V (a x : ℝ) : Set ℂ := ({s | a < s.re} ∩ tilt x) ∩ ({s | s.im < 1} ∩ {s | -1 < s.im})

/-- The seed point `s₀ = (3 - x)/2 + (3/4) i`; it has real part `> 1` when `x < 1`. -/
noncomputable def seed (x : ℝ) : ℂ := ⟨(3 - x) / 2, 3 / 4⟩

lemma kappa_mul (hx : x < 1) : (1 - x) * kappa x = 1 / 2 := by
  unfold kappa
  have : (1 - x) ≠ 0 := by linarith
  field_simp

lemma kappa_pos (hx : x < 1) : 0 < kappa x := by
  unfold kappa
  exact inv_pos.mpr (by linarith)

lemma isLinearMap_tilt (x : ℝ) : IsLinearMap ℝ (fun s : ℂ => s.re * kappa x - s.im) :=
  { map_add := fun s t => by simp only [add_re, add_im]; ring
    map_smul := fun c s => by simp only [smul_re, smul_im, smul_eq_mul]; ring }

lemma convex_tilt (x : ℝ) : Convex ℝ (tilt x) :=
  convex_halfSpace_lt (isLinearMap_tilt x) _

lemma isOpen_tilt (x : ℝ) : IsOpen (tilt x) :=
  isOpen_lt ((continuous_re.mul continuous_const).sub continuous_im) continuous_const

lemma convex_V (a x : ℝ) : Convex ℝ (V a x) :=
  ((convex_halfSpace_re_gt a).inter (convex_tilt x)).inter
    ((convex_halfSpace_im_lt 1).inter (convex_halfSpace_im_gt (-1)))

lemma isOpen_V (a x : ℝ) : IsOpen (V a x) :=
  (((isOpen_lt continuous_const continuous_re).inter (isOpen_tilt x)).inter
    ((isOpen_lt continuous_im continuous_const).inter (isOpen_lt continuous_const continuous_im)))

lemma isPreconnected_V (a x : ℝ) : IsPreconnected (V a x) :=
  (convex_V a x).isPreconnected

lemma ofReal_mem_V (hax : a < x) (hx1 : x < 1) : (x : ℂ) ∈ V a x := by
  have hk := kappa_pos hx1
  simp only [V, tilt, mem_inter_iff, mem_setOf_eq, ofReal_re, ofReal_im]
  refine ⟨⟨hax, ?_⟩, by norm_num, by norm_num⟩
  linarith

lemma one_notMem_V (hx1 : x < 1) : (1 : ℂ) ∉ V a x := by
  have hk := kappa_mul hx1
  intro h
  obtain ⟨⟨_, h2⟩, _⟩ := h
  simp only [tilt, mem_setOf_eq, one_re, one_im] at h2
  linarith

lemma seed_re (x : ℝ) : (seed x).re = (3 - x) / 2 := rfl
lemma seed_im (x : ℝ) : (seed x).im = 3 / 4 := rfl

lemma seed_mem_V (hax : a < x) (hx1 : x < 1) : seed x ∈ V a x := by
  have hk := kappa_mul hx1
  have hk0 := kappa_pos hx1
  have h3 : ((3 - x) / 2) * kappa x = x * kappa x + 3 / 4 := by linear_combination (3 / 2) * hk
  simp only [V, tilt, mem_inter_iff, mem_setOf_eq, seed_re, seed_im]
  refine ⟨⟨by linarith, ?_⟩, by norm_num, by norm_num⟩
  linarith

lemma one_lt_seed_re (hx1 : x < 1) : 1 < (seed x).re := by
  rw [seed_re]; linarith

lemma V_subset (a x : ℝ) (hx1 : x < 1) :
    V a x ⊆ {s : ℂ | a < s.re ∧ |s.im| < 1} \ {1} := by
  intro s hs
  have hs' := hs
  simp only [V, tilt, mem_inter_iff, mem_setOf_eq] at hs'
  refine ⟨⟨hs'.1.1, abs_lt.mpr ⟨hs'.2.2, hs'.2.1⟩⟩, ?_⟩
  intro h1
  exact one_notMem_V hx1 (mem_singleton_iff.mp h1 ▸ hs)

lemma V_subset_re_gt_sdiff (a x : ℝ) (hx1 : x < 1) :
    V a x ⊆ {s : ℂ | a < s.re} \ {1} :=
  fun s hs => ⟨((V_subset a x hx1) hs).1.1, ((V_subset a x hx1) hs).2⟩

/-- **Identity theorem on `V`.** If `F` and `G` are holomorphic on `V a x` and agree on the
half-plane `{s | 1 < re s}`, they agree on all of `V a x`. -/
theorem eqOn_V_of_eqOn_re_gt_one {F G : ℂ → ℂ} {a x : ℝ} (hax : a < x) (hx1 : x < 1)
    (hF : DifferentiableOn ℂ F (V a x)) (hG : DifferentiableOn ℂ G (V a x))
    (h : ∀ s : ℂ, 1 < s.re → F s = G s) : EqOn F G (V a x) := by
  have hFa : AnalyticOnNhd ℂ F (V a x) := hF.analyticOnNhd (isOpen_V a x)
  have hGa : AnalyticOnNhd ℂ G (V a x) := hG.analyticOnNhd (isOpen_V a x)
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hmem : {s : ℂ | 1 < s.re} ∈ nhds (seed x) :=
    hopen.mem_nhds (by simpa only [mem_setOf_eq] using one_lt_seed_re hx1)
  have hfg : F =ᶠ[nhds (seed x)] G := Filter.eventually_of_mem hmem fun s hs => h s hs
  exact hFa.eqOn_of_preconnected_of_eventuallyEq hGa (isPreconnected_V a x) (seed_mem_V hax hx1) hfg

/-- **Continuation to a real point.** If `F` and `G` are holomorphic on `V a x` and agree on
`{s | 1 < re s}`, then `F x = G x` for the real point `x ∈ (a, 1)`. -/
theorem eq_at_ofReal_of_eqOn_re_gt_one {F G : ℂ → ℂ} {a x : ℝ} (hax : a < x) (hx1 : x < 1)
    (hF : DifferentiableOn ℂ F (V a x)) (hG : DifferentiableOn ℂ G (V a x))
    (h : ∀ s : ℂ, 1 < s.re → F s = G s) : F x = G x :=
  eqOn_V_of_eqOn_re_gt_one hax hx1 hF hG h (ofReal_mem_V hax hx1)

/-- The same, with holomorphy assumed on the punctured half-plane `{s | a < re s} \ {1}`. -/
theorem eq_at_ofReal_of_differentiableOn_sdiff {F G : ℂ → ℂ} {a x : ℝ} (hax : a < x)
    (hx1 : x < 1) (hF : DifferentiableOn ℂ F ({s : ℂ | a < s.re} \ {1}))
    (hG : DifferentiableOn ℂ G ({s : ℂ | a < s.re} \ {1}))
    (h : ∀ s : ℂ, 1 < s.re → F s = G s) : F x = G x :=
  eq_at_ofReal_of_eqOn_re_gt_one hax hx1 (hF.mono (V_subset_re_gt_sdiff a x hx1))
    (hG.mono (V_subset_re_gt_sdiff a x hx1)) h

/-- The same, with holomorphy assumed on the punctured strip
`{s | a < re s ∧ |im s| < 1} \ {1}` (for representations with singularities elsewhere on the
line `re s = 1`, such as `η(s) / (1 - 2^{1-s})`). -/
theorem eq_at_ofReal_of_differentiableOn_strip {F G : ℂ → ℂ} {a x : ℝ} (hax : a < x)
    (hx1 : x < 1) (hF : DifferentiableOn ℂ F ({s : ℂ | a < s.re ∧ |s.im| < 1} \ {1}))
    (hG : DifferentiableOn ℂ G ({s : ℂ | a < s.re ∧ |s.im| < 1} \ {1}))
    (h : ∀ s : ℂ, 1 < s.re → F s = G s) : F x = G x :=
  eq_at_ofReal_of_eqOn_re_gt_one hax hx1 (hF.mono (V_subset a x hx1))
    (hG.mono (V_subset a x hx1)) h

end CN1.CS
