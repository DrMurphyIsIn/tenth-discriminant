# Palomar sources for the RH certificate work (2026-09-08)

Curated from the Palomar registry (`https://data.palomar-registry.org/recent.json`,
Lean-verified + comparator-checked formalizations). These entries either already
formalize a roadmap *reduction* (reuse/cite), provide certificate-shaped math
Telperion can emit, or supply enabling infrastructure. Mined + maintained by
`telperion palomar-mine --topic rh` (see `PALOMAR_MINING.md`).

Honesty invariant unchanged: everything here supports the *positive-proportion /
reduction* program; `conjecture1_proved = False`. A Palomar entry is a lead, not
an emitter — build + CI-verify.

## Track 2 (Li's criterion) — the reduction is ALREADY formalized; reuse it
- **`PALOMAR-2026-09-05-000005`** — *Li's criterion for the Riemann Hypothesis*
  (`nicholasbulka/li-criterion-rh-equivalence-lean`). Against Mathlib's
  `RiemannHypothesis`: **RH ⟺ every Li–Keiper coefficient of ξ has nonnegative
  real part**, and identifies the analytic coefficient (Taylor coeff of the
  log-derivative of `s ↦ ξ(1/(1−s))`) with the arithmetic zero-sum coefficient.
  → Build the Li positivity-ladder emitter to discharge `λ_n ≥ 0` for finite n
  *onto this reduction*, not from scratch. (candidate NEW shape: "Li positivity ladder")

## Track 1 (Jensen–Pólya) — the Laguerre/Turán layer
- **`PALOMAR-2026-08-27-000002`** — *csordas-comparator* (`BrandonMYates/csordas-comparator`).
  Laguerre/Turán expressions `J_n(t) = (Φ⁽ⁿ⁾)² − Φ⁽ⁿ⁻¹⁾Φ⁽ⁿ⁺¹⁾` for Riemann's Φ-kernel
  (a counterexample to a Coffey–Csordas log-concavity conjecture). Turán = degree-2
  Jensen hyperbolicity; the concrete Φ-coefficient machinery + a cautionary counterexample.
- **`PALOMAR-2026-08-27-000001`** — *tempered-xi-comparator* — de Bruijn–Newman / Pólya
  zero-geometry of Riemann's kernel. DBN-constant adjacent.

## Track 3 (Weil positivity) + HermitianMomentInertia — pair-correlation engine + negative control
- **`PALOMAR-2026-08-21-000004`** — *zeta-lab* (`teal-sea/zeta-lab`): the Fredholm variational
  identity `A = I + T` with the **Farmer–Gonek–Lee pair-correlation form factor F1**. The
  analytic engine behind zeta-23's Theorem D constant `c₁*` — feeds the κ-optimization in
  our `TwoMomentCountEmitter`.
- **`PALOMAR-2026-08-25-000005`** — *zeta-lab*: states zeta-23's **Theorem D** (`H = 0.67250…`)
  for Mathlib's `riemannZeta`; points to `ainta/zeta-simple-zeros` refining it.
- **`PALOMAR-2026-08-21-000012`** — *zeta-lab*: **Davenport–Heilbronn** (functional equation,
  zeros OFF the line — RH-false). The **negative control**: any certificate family that
  "proves too much" would falsely certify D-H. Wire as a negative-control adapter.
- **`PALOMAR-2026-08-29-000004`** — `yuhangshi888/zeta-simple-zeros`: supporting-plane +
  exact-arithmetic finite-dimensional simple-zeros argument.

## Track 4 (Hilbert–Pólya / spectral) — enabling infrastructure now exists
- **`PALOMAR-2026-09-01-000004`** — *lean-spectral-theory* (`savarin/lean-spectral-theory`):
  spectral theorem for **unbounded self-adjoint operators** (Cayley transform + PVMs) + Stone's
  theorem. The substrate needed to even *state* a Hilbert–Pólya operator (real spectrum = zeros).
- **`PALOMAR-2026-09-01-000002`** — *lean-operator-theory*: von Neumann polynomial inequality +
  Crouzeix–Palencia.

## Cross-cutting certificate backing (Telperion SOS/PSD/inertia)
- **`PALOMAR-2026-09-07-000002`** — Bollobás–Nikiforov (semidefinite/spectral eigenvalue, 15B48/15A18).
- **`PALOMAR-2026-08-20-000002`** — Low-Rank Univariate SOS (Legat–Yuan–Parrilo) → SOS/PSD emitters.
- **`PALOMAR-2026-09-02-000014`** — trace-form / **signature product rule** (Sylvester inertia).

## Actions
1. Track 2: Li positivity-ladder emitter onto `li-criterion-rh-equivalence-lean`.
2. Wire Davenport–Heilbronn as the HermitianMomentInertia negative control.
3. Reuse the Farmer–Gonek–Lee form factor for the `TwoMomentCountEmitter` κ-optimization.
4. Track 4: use `lean-spectral-theory` to formalize a Hilbert–Pólya *statement*.
5. Bidirectional: our certificates fit `PalomarTemplate`/comparator — submit back.
