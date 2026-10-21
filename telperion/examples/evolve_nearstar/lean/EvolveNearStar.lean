import Mathlib

namespace Telperion

/-- If `f : ℕ → ℝ` rises up to `sstar` and falls beyond it, then its maximum
over `n ≥ s0` is at `sstar`. -/
theorem unimodal_peak {f : ℕ → ℝ} {s0 sstar : ℕ}
    (hup : ∀ s, s0 ≤ s → s < sstar → f s ≤ f (s + 1))
    (hdn : ∀ s, sstar ≤ s → f (s + 1) ≤ f s) :
    ∀ n, s0 ≤ n → f n ≤ f sstar := by
  have climb : ∀ a b, s0 ≤ a → a ≤ b → b ≤ sstar → f a ≤ f b := by
    intro a b ha hab hb
    induction hab with
    | refl => exact le_refl _
    | @step k hk ih =>
      have hks : k < sstar := lt_of_lt_of_le (Nat.lt_succ_self k) hb
      exact le_trans (ih (le_of_lt hks)) (hup k (le_trans ha hk) hks)
  have desc : ∀ a b, sstar ≤ a → a ≤ b → f b ≤ f a := by
    intro a b ha hab
    induction hab with
    | refl => exact le_refl _
    | @step k hk ih => exact le_trans (hdn k (le_trans ha hk)) ih
  intro n hn
  rcases (by omega : n ≤ sstar ∨ sstar < n) with h | h
  · exact climb n sstar hn h le_rfl
  · exact desc sstar n le_rfl (le_of_lt h)

/-- Bridge: from a positive sequence whose successor ratio is `≥ 1` below `sstar`
and `≤ 1` at/above it, derive the pointwise climb/descend hypotheses
`unimodal_peak` needs. Lets a caller assemble the full `f n ≤ B` theorem from a
Pólya-certified decreasing ratio plus the two crossing facts. -/
theorem climb_descend_of_ratio
    (f : ℕ → ℝ) (s0 sstar : ℕ) (hs0 : s0 ≤ sstar)
    (hpos : ∀ s, s0 ≤ s → 0 < f s)
    (hrup : ∀ s, s0 ≤ s → s < sstar → 1 ≤ f (s + 1) / f s)
    (hrdn : ∀ s, sstar ≤ s → f (s + 1) / f s ≤ 1) :
    (∀ s, s0 ≤ s → s < sstar → f s ≤ f (s + 1)) ∧
    (∀ s, sstar ≤ s → f (s + 1) ≤ f s) := by
  refine ⟨?_, ?_⟩
  · intro s hs hlt
    have hp : 0 < f s := hpos s hs
    have h := hrup s hs hlt
    rw [le_div_iff₀ hp] at h
    linarith
  · intro s hs
    have hp : 0 < f s := hpos s (le_trans hs0 hs)
    have h := hrdn s hs
    rw [div_le_one hp] at h
    linarith

end Telperion


namespace EvolveNearStar

theorem evolve_nearstar_dec (t : ℝ) (ht : 0 ≤ t) : (0:ℝ) ≤ (233583317350348748266395810 + 6112157103512513253191313432 * t + 77629861232853219523497978450 * t ^ 2 + 637666712576491251022078121280 * t ^ 3 + 3808393487000604292715130160350 * t ^ 4 + 17627481957950754223261593233304 * t ^ 5 + 65817855530450326204763347681470 * t ^ 6 + 203750285081759725184497592931312 * t ^ 7 + 533401599215962272929981365273140 * t ^ 8 + 1198613855434148782360387206872112 * t ^ 9 + 2338708444326982125775762475973300 * t ^ 10 + 3998480181566207752890611565716160 * t ^ 11 + 6033930399068553915664459472855100 * t ^ 12 + 8084452321564597231967601441235440 * t ^ 13 + 9663257479018879611844416765315900 * t ^ 14 + 10344395758197537186894237672284832 * t ^ 15 + 9948420019505689719931837904040810 * t ^ 16 + 8616862171304895456821931282903096 * t ^ 17 + 6734774196668878107698082805757370 * t ^ 18 + 4756498937923518964646089974449856 * t ^ 19 + 3038432725311354021686454540697950 * t ^ 20 + 1756400187035772067405000628683440 * t ^ 21 + 918827872420663652236844715144000 * t ^ 22 + 434828667023603806204865215641600 * t ^ 23 + 186002120205484526090469288384000 * t ^ 24 + 71824186963743838865312700321792 * t ^ 25 + 24991464671264691249653994946560 * t ^ 26 + 7817154236834662460962888482816 * t ^ 27 + 2191429773922656285324910264320 * t ^ 28 + 548510561090642709743954558976 * t ^ 29 + 122006670134363643675389460480 * t ^ 30 + 23977417540713447629286014976 * t ^ 31 + 4133440399390734863145369600 * t ^ 32 + 619430333830029508230512640 * t ^ 33 + 79775524248192848756736000 * t ^ 34 + 8699614703397551336325120 * t ^ 35 + 787595190723952194355200 * t ^ 36 + 57596838845044878213120 * t ^ 37 + 3268841616619182489600 * t ^ 38 + 135076190944839598080 * t ^ 39 + 3614963334685655040 * t ^ 40 + 47023913296723968 * t ^ 41) / (529 * (3 + 4 * t) * (3 + 4 * t) * (3 + 4 * t) * (3 + 4 * t) * (3 + 4 * t) * (3 + 4 * t) * (3 + 4 * t) * (3 + 4 * t) * (3 + 4 * t) * (3 + 4 * t) * (3 + 4 * t) * (7 + 4 * t) * (7 + 4 * t) * (7 + 4 * t) * (7 + 4 * t) * (7 + 4 * t) * (7 + 4 * t) * (7 + 4 * t) * (7 + 4 * t) * (7 + 4 * t) * (7 + 4 * t) * (7 + 4 * t) * (2 + t) * (2 + t) * (2 + t) * (2 + t) * (2 + t) * (2 + t) * (2 + t) * (2 + t) * (2 + t) * (2 + t) * (2 + t) * (3 + t) * (3 + t) * (3 + t) * (3 + t) * (3 + t) * (3 + t) * (3 + t) * (3 + t) * (3 + t) * (3 + t) * (3 + t)) := by positivity
theorem evolve_nearstar_cross_hi : ((980170052528609401200979968 / 996644577901404223353123569) : ℝ) ≤ 1 := by norm_num
theorem evolve_nearstar_cross_lo : (1:ℝ) ≤ (87946907297998046875 / 86959512306484890624) := by norm_num

-- Evolve-discovered champion (structured/LLM-free, seed=0): ratio_src = 486/529 * (1 + 1/(4*s**2 + 11*s + 6))**11, s0 = 0, lift_max = 0.
-- The 3 theorems above are the reusable ratio certificate (Pólya-decreasing step + crossing of 1 at s* = 5).
-- To conclude `f n ≤ f 5` for the caller's sequence f, apply `Telperion.unimodal_peak` against f's own definition.

end EvolveNearStar
