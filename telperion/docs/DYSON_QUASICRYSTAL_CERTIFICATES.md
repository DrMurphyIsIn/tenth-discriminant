# Dyson quasicrystal → certificate-shaped mathematics (deep research, 2026-09-09)

Adversarially-verified research report (deep-research harness: 21 primary sources fetched,
103 claims extracted, 25 verified by 3-vote adversarial panels — **24 confirmed, 1 refuted**)
on Freeman Dyson's 2009 "quasicrystal" framing of RH, triaged into Telperion certificate
shapes. `conjecture1_proved = False`; category discipline enforced throughout.

## The framing (verified 3-0, Dyson, Notices AMS 56(2) 2009)

**IF RH holds**, the nontrivial zeta zeros form a 1-D Fourier quasicrystal — a pure-point
measure whose distributional Fourier transform is also pure-point (Bragg peaks read off the
Guinand–Weil explicit formula). Dyson's proposed route: *classify all 1-D quasicrystals, find
zeta's among them* — which he himself calls "horrendously difficult." The classification is
the RH-hard object; it is NOT a finite certificate.

**REFUTED (0-3):** "the zeta-zero diffraction spectrum is supported exactly on {log p^k}" —
that support statement is *RH-conditional* (Dyson's heuristic reading), not an established
diffraction fact. Any certificate must treat Bragg-peaks-on-{log p^k} as a conditional target.

## Category triage (the deliverable)

### (a) The one genuine iff — and why it does not close RH
**Every 1-D ℕ-valued Fourier quasicrystal = a Kurasov–Sarnak measure from a Lee–Yang
polynomial** (Kurasov–Sarnak JMP 61:083501 2020 / arXiv:2006.12037; Alon–Cohen–Vinzant
arXiv:2307.13498, Inventiones 2024; Olevskii–Ulanovskii). Support = real zero set of
`p(exp(ixl))`, amplitudes = integer multiplicities; conversely every real-rooted exponential
polynomial lifts to a Lee–Yang polynomial on a positive torus line. This rigorously realizes
Dyson's classification — **but only for ℕ-valued FQs, and the zeta measure is provably NOT
one** (Kurasov–Sarnak verbatim: "the explicit formula in the theory of primes does not give
a Fourier quasicrystal"). So the iff exists, closes the *analogue* class, and leaves RH
untouched. That gap IS the honest ceiling.

### (b) Finite-checkable, certificate-shaped — build these (structural analogues, NOT RH)
1. **Lee–Yang / stable-pair real-rootedness** (→ our `interlacing` + Hermitian-inertia
   shapes): `p` Lee–Yang ⟺ no zeros in D^n ∪ (ℂ\D̄)^n; Möbius-equivalent to real
   stability; canonical determinantal form `det(diag(z)+U)`, U unitary (a Hermitian-
   eigenvalue object). Stability of (P,Q) FORCES all zeros of the derived finite Dirichlet
   series onto Re(s)=0 — zeros-on-the-line *by construction*. → new emitter candidate
   `lee_yang_stable_pair`.
2. **Closed-form Bragg amplitudes / finite-height explicit formula** (→ the in-progress
   "Bragg amplitude in closed form" + `rect_explicit_formula` work): Kurasov–Sarnak Eq. 27
   — Σ_{zeros} ĥ(γ) = (ξ·l)h(0) − Σ_k (ξ·k)c_P(k)h(ξ·k) − …, with c_P(k) an EXACT finite
   rational multinomial over compositions; Olevskii–Ulanovskii residue coefficients
   c_λ = ψ(λ)/φ′(λ). Kernel-checkable at finite height (after pairing with a compactly-
   supported test function — the raw index set is infinite; that pairing is load-bearing).
3. **Rouché winding + interval-enclosure real-rootedness** (→ our `argument_principle` +
   enclosure shapes): the OU worked example `sin(πz) + δ·sin z` (0<δ≤1/2) is proved
   real/simple/uniformly-discrete-rooted by |sin πz| > δ|sin z| on contour squares +
   one-zero-per-interval sign checks. **Lean gap flagged:** the paper's "n large enough" must
   become an explicit contour bound N for a kernel certificate.
4. **Finite algebraic periodicity criteria** (→ `finite_decide`): irreducible/binomial
   factorization of the Lee–Yang polynomial decides periodicity vs genuine quasiperiodicity
   (Alon–Vinzant Thm 1.5/1.11 — a semi-algebraic, finitely-decidable locus).
5. **Favorov gate** (arXiv:2311.02728): absolutely-convergent Dirichlet series with bounded
   spectrum + only real zeros ⟹ pure-point diffraction (sufficient, not iff) — the
   real-rootedness→pure-point infrastructure lemma.

### (c) RH-hard — never emit as if finite
Uniform O(1)-amplitude / equal-asymptotic-height statements; positivity of the FULL infinite
diffraction/Weil functional; the general (non-ℕ-valued) crystalline-measure classification.
**Time-sensitivity warning (verified):** arXiv:2410.03673 (Shaughnessy) v4 explicitly denies
any reduction ("linear arrangement of spectral peaks does NOT imply β=1/2") but later
versions (v6–v12) REVERSE and claim a full RH proof via an O(1)-amplitude self-duality
argument — single-author, non-peer-reviewed, contested, itself RH-hard. Do not treat as
established.

## Open questions (from the verified panel)
- Emit Kurasov–Sarnak Eq. 27 for a specific stable polynomial as an exact-rational Lean cert
  (category-b analogue, honestly labeled non-RH)?
- Make the Rouché cert fully finite (explicit N) and generalize to a real-rootedness template
  for exponential polynomials?
- Does `det(diag(z)+U)` admit a direct Hermitian-inertia certificate; can multivariate real
  stability reduce to a finite SOS/PSD condition?
- The de Branges / Hilbert–Pólya angle surfaced NO concrete finite PSD-Gram certificate in
  2015–2026 literature — that lane remains open.

## Palomar gap
No crystalline-measure / Fourier-quasicrystal formalization exists in the Palomar registry
(checked 2026-09-09) — the Kurasov–Sarnak construction is finite, Lean-formalizable, and a
clean submission opportunity.

Sources (primary, verified against PDFs): Kurasov–Sarnak arXiv:2006.12037/JMP 2020;
Alon–Cohen–Vinzant arXiv:2307.13498 + Inventiones 2024 (s00222-024-01307-8);
Olevskii–Ulanovskii; Favorov arXiv:2311.02728; Dyson, Notices AMS 56(2) 2009;
Shaughnessy arXiv:2410.03673 (v4 vs v6+ divergence noted); GORZ arXiv:1902.07321.

## Addendum (2026-09-09): arXiv:2410.03673 v8 reviewed specifically
v8 (Jan 2026, Shaughnessy, quant-ph) CLAIMS a full RH proof ("Fourier self-duality of the
prime quasicrystal forces all non-trivial zeros to lie on Re(s)=1/2", Appendix "Proof of the
Riemann Hypothesis", Thm A.2) — reversing the author's own v4 Thm A.3 (verified 3-0 above).
Assessment: NOT established. (1) The self-duality premise presupposes the zeta measure is
pure-point-with-pure-point-transform — the {log p^k}-support claim our panel REFUTED 0-3 as
unconditional, and Kurasov–Sarnak prove the technical FQ version false even under RH.
(2) The "dimensional constraint" (uniform amplitudes forced by "one-dimensional duality") is
not a theorem — weighted Dirac combs are valid tempered distributions; the paper's A.3 is
"intuitive reasoning about scale-dependence," i.e. the category-(c) uniform-amplitude step
ASSERTED, not proved. (3) Remainder R_L(k) dismissed without uniform control; no tempered-
distribution treatment of the infinite sum. Provenance: single-author, 12 versions with a
flipped conclusion, LLM acknowledgements, no peer review/formalization. Treat as category-(c)
claimed; the v4 finite scattering construction remains the only absorbed (category-b) content.
