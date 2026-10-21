# Li positivity-ladder emitter (RH-roadmap Track 2)

Certifies finite prefixes of **Li's criterion** onto the *already-formalized* upstream
reduction, surfaced by the Palomar miner:

    nicholasbulka/li-criterion-rh-equivalence-lean
    LiCriterion.li_criterion_rh_iff :
        RiemannHypothesis ↔ (∀ n : ℕ, 0 ≤ (taylorCoeff riemannXi n).re)

(`liSummand n ρ = 1 − (1 − 1/ρ)^{−(n+1)}`; the RHS is the Li–Keiper positivity ladder.)

## What the emitter does

`LiPositivityLadderEmitter` (kind `li_positivity`) emits, per rung `n`:

    theorem li_rung_<n> (hlo : (lo : ℝ) ≤ (taylorCoeff riemannXi n).re) :
        0 ≤ (taylorCoeff riemannXi n).re :=
      le_trans (by norm_num : (0:ℝ) ≤ lo) hlo

- `lo` is a **certified positive rational lower bound** on the n-th ξ Taylor coefficient's
  real part. `certify` refuses `lo ≤ 0` (a non-positive bound cannot witness positivity) and `n < 0`.
- The claim is **load-bearing**: it is about the ACTUAL `(taylorCoeff riemannXi n).re`, not an
  abstract real — so it is non-vacuous.

## Trust seam (documented, honest)

`hlo` — the lower bound `lo ≤ (taylorCoeff riemannXi n).re` — is an EXTERNAL numeric input
(Arb / mpmath interval arithmetic on ξ's Taylor coefficient at 0), carried as a theorem
HYPOTHESIS. The kernel proves only `0 ≤ lo ⟹ 0 ≤ coeff`; it does NOT evaluate the
transcendental coefficient. Same discipline as the RH-in-a-box Arb enclosures and the
effective-dVP inputs.

## Honest ceiling

Each rung is a finite verification. The **uniform `∀ n`** is exactly the RHS of
`li_criterion_rh_iff` — i.e. **RH itself**. Certifying rungs 0..N is NOT progress toward RH;
it is the certificate-shaped, generator-producible prefix of a reduction whose tail is RH.
`conjecture1_proved = False`.

## Wiring status / TODO

- Emitter + `certify` + registry wiring + Python tests: DONE (this branch), classification green.
- The emitted rungs `import Lc.LiCriterion.XiOrderBridge`; **CI compilation needs the upstream
  `li-criterion-rh-equivalence-lean` as a lake dependency** (add a `require` to a new
  `examples/li_positivity/lean/lakefile.toml`, mirroring how `zeta_zero_localization` requires
  its sibling `zero_free_bridge`). Until wired, rungs are emitted-but-not-CI-compiled.
- NEXT: an Arb finder (`enclose_xi_taylor_coeff`) that computes the rigorous `lo` per n
  (reuse/extend `telperion.arb_enclosure`), turning the trust-seam hypothesis into a produced
  certificate — then assemble `∀ n < N, 0 ≤ (taylorCoeff riemannXi n).re` and cite
  `li_criterion_rh_iff` for the "first N rungs verified" statement.
- Reuse the RvM/explicit-formula foundation (`RVM_EXPLICIT_FORMULA_FOUNDATION.md`,
  `DiffractionCore.rect_explicit_formula`) if expressing λ_n via the arithmetic side later.

## The finished ladder (2026-09-09)

The original PR (#393) shipped the emitter with a single hand-picked rung. The finish
replaces that with the full generated ladder:

- **Rigorous backend** — `telperion.li_coeff.enclose_li_coeffs`: exact-rational outward
  enclosures of `taylorCoeff riemannXi n` via python-flint ball arithmetic. The series
  route never meets the ζ-pole: by the functional equation `ξ(1/(1−z)) = ξ(g(z))` with
  `g = −z/(1−z)`, and at 0 the completed form `ξ(s) = (s−1)·π^{−s/2}·Γ(s/2+1)·ζ(s)` is
  analytic factor-by-factor (`s·Γ(s/2)` absorbed into `Γ(s/2+1)`; `ζ(0) = −1/2`). The
  Li coefficients are read off `F′/F`. Self-check: the first three enclosures must
  contain the PUBLISHED Li–Keiper values (Keiper 1992 / Li 1997 / Coffey 2004) or the
  backend refuses — an external anchor against normalization/index bugs.
- **Twenty rungs** — `examples/li_positivity/generate.py` regenerates
  `lean/LiPositivity.lean` (drift-checked; manifest group `flint`): rungs `n = 0..19`
  with lower bounds rounded DOWN to 12 significant decimals (still rigorous, readable
  literals). λ₁ through λ₂₀ are all certified positive.
- **The falsifiability face** — `li_neg_refutes_rh`: a certified NEGATIVE upper bound
  on any rung refutes RH outright through `li_criterion_rh_iff` (term-mode proof).
  Never expected to fire; it makes the ladder falsifiable, not confirmation-only.
- **Axiom guard** — `AxiomGuardLiPositivity.lean` re-verifies (at our pin) that the
  rungs, the refutation atom, and the upstream `li_criterion_rh_iff` itself use only
  the three Mathlib axioms.
- **Negative control** — `negctrl_adapters/adapter_li_positivity.py`: a sign-corrupted
  lower bound (`lo = −1/100`, minted past the Layer-1 refusal) must be kernel-rejected
  at the in-proof `norm_num` gate; the `+1/100` twin compiles.
- **CI** — `li-positivity-compiles` in telperion-lean-e2e: regenerate `--check`, then
  `lake build` against the pinned upstream (toolchain island v4.34.0-rc1), then the
  axiom guard.

Still true, and stated everywhere: the uniform `∀ n` IS RH; twenty rungs are a finite
necessary-condition check and no progress toward it. `conjecture1_proved = False`.
