# Telperion

Telperion turns mathematical claims that are too numerous or too tedious to prove by hand into Lean 4
theorems that the Lean kernel checks. You describe a *family* of claims (an inequality with parameters,
a table of finite facts, an identity, an enclosure of a constant), Telperion finds a certificate for each
member in exact arithmetic, and it writes out Lean files whose proofs replay those certificates. Then Lean
checks them.

It was built for computer-assisted proofs, where the conceptual argument fits in a paper but rests on
hundreds or thousands of concrete inequalities that a referee cannot realistically check by hand.

To see Telperion at work before reading further, open the
[Telperion registry explorer](https://drmurphyisin.github.io/brualdi-goldwasser/telperion-explorer/).
It walks through the Brualdi-Goldwasser theorem (the first research program to reach its goal) with live
plots, then shows the whole missions registry: every formal statement Telperion tracks, with its status,
dependencies and verification record, and the open Riemann-hypothesis campaigns.

## The trust model

The whole design follows from one rule: **the generator is untrusted, and the Lean kernel is the only
trusted component.**

Telperion is a large Python program, and large programs have bugs. So nothing it computes is taken on
faith. Every certificate becomes a Lean proof, and the kernel re-checks it from scratch. If the generator
is wrong, whether through a bug, a floating-point slip, or a claim that was never true, the result is a
Lean file that does not compile, not a false theorem. A wrong certificate is a failed build.

That means the Python checks inside Telperion are there to catch mistakes early and to explain them, not
to establish truth. It also means the part a human must still check is the *statement*: whether the
theorems Lean accepts say what you meant. Several of the tools below exist to make that check easier.

## How it works

```
family ──► certify ──► validate ──► emit ──► Lean files ──► Lean kernel
            │                        │
            └─ refuse + diagnose     └─ provenance hash, freeze, drift check
```

1. **Describe a family.** A family is a finite grid of instances. The basic kind is a claim `0 ≤ target`
   about rational functions of nonnegative real variables. Others are bilinear box claims (`before ≤
   after` on a rectangle), identities, finite decidable facts, and existential "one of these witnesses
   works" claims. A family can also declare *ties* (points where the claim must be exactly tight, so an
   overclaim with slack is refused), *anchors* (known values the pipeline must reproduce), and an
   *independent implementation* of the target, which is cross-checked at random rational points so that
   a bug in one engine is caught by the other.
2. **Certify.** For every instance Telperion looks for a certificate in exact arithmetic (sympy over
   rationals, never floats). For the basic kind this is a Pólya certificate: the claim's numerator has only
   nonnegative coefficients over a positive denominator, which makes nonnegativity evident. If an instance
   cannot be certified, Telperion refuses to go further and says why. The claim may be false (it then
   searches for an exact rational counterexample), true but not certifiable in this form (it suggests
   transformations), or set up wrongly.
3. **Validate.** An exact numeric layer of rational interval arithmetic and verified constants checks the
   family's side conditions. Emission is refused unless validation is green.
4. **Emit.** Deterministic templates turn each certificate into a Lean theorem, respecting your project's
   imports, namespace and prelude. Every file starts with a header carrying a SHA-256 hash of everything
   that determined it: the family, the grid, the expressions, the Lean profile and the templates.
   Timestamps are deliberately left out, so identical inputs produce byte-identical files.
5. **Freeze and compare.** `freeze` stores the emitted files with a manifest; `diff_frozen` regenerates a
   family and reports any drift. A certificate directory can therefore be audited by regenerating it,
   without reading thousands of lines of generated Lean.

## A small example

```python
import sympy as sp
from telperion.family import InequalityFamily, GridSpec
from telperion.certify import certify
from telperion.emit import DirectPolyaEmitter
from telperion.lean import LeanProfile
from telperion.workflow import emit, ValidationReport

x = sp.Symbol("x", nonnegative=True)
fam = InequalityFamily(
    name="demo",
    symbols=(x,),
    grid=GridSpec([("k", range(1, 4))]),
    lean_name=lambda pt: f"demo_nonneg_{pt['k']}",
    # the claim: 0 <= (x^2 + k x + 1) / (x + k) for all x >= 0, for k = 1, 2, 3
    target=lambda pt: (x**2 + pt["k"] * x + 1) / (x + pt["k"]),
)
result = emit(certify(fam), LeanProfile(namespace=("Demo",)), [DirectPolyaEmitter()],
              ValidationReport.from_asserts([("claim is well-posed", lambda: None)]))
print(list(result.files.values())[0])
```

This prints a Lean file with three theorems, one per value of `k`, such as

```lean
theorem demo_nonneg_2 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (1 + 2 * x + x ^ 2) / ((2 + x)) := by
  have hd1 : (2 + x : ℝ) ≠ 0 := by positivity
  ...
  positivity
```

and Lean with Mathlib accepts it. Change the target to the false claim `x - 1` and `certify` stops before
any Lean is written:

```
CertificationError: 1 instance(s) failed certification:
  {'k': 1}: numerator not all-nonneg-integer: [((0,), -1)]
```

(Both behaviours were checked for this README against Lean 4 v4.32.0 and Mathlib v4.32.0.)

## What it can certify

The engine has 169 *emitter* modules, each for one family of certificate shapes. Each pairs an exact-arithmetic certificate
check with a Lean proof template. The main groups are:

- **Positivity of rational functions:** Pólya certificates, bilinear boxes reduced to their corners,
  Bernstein and Handelman forms, orthant and domain transformations.
- **Sums of squares and algebraic certificates:** rational SOS and Gram matrices, constrained SOS,
  Positivstellensatz-style multipliers, Nullstellensatz and real-Nullstellensatz refutations, Farkas and
  cone certificates, infeasibility.
- **Identities and telescopes:** rational-function identities on a ray, forward telescopes, recurrences.
- **Finite facts:** guarded universally quantified statements over explicit tables, proved by kernel
  evaluation (`decide +kernel`), with tables encoded as natural-number bitmasks and fixed-point integers
  so that the kernel can evaluate them efficiently.
- **Enclosures of transcendental quantities:** rigorous rational brackets for `exp` and `log` at rational
  points, threshold and Laurent-type bounds, and ball-arithmetic (Arb) enclosures for analytic
  quantities.
- **Complex analysis:** argument-principle and zero-counting certificates, zero-free regions, and bounds
  used in analytic number theory.

The [complete list](#all-emitters) is at the end of this README; each module's docstring states its
claim shape, its certificate, and what it refuses.

## Making the kernel do the work

Big certificates meet a practical obstacle: the Lean kernel is fast at some things and very slow at
others. The emitters follow a set of rules learned the hard way:

- **Arithmetic over ℚ is slow in the kernel**, because normalizing a rational number goes through a
  well-founded gcd, so large checks use ℕ and ℤ (and fixed point) and small ones use ℚ.
- **Well-founded recursion does not reduce well in the kernel**, so recursive checks use structural
  recursion with an explicit fuel argument.
- **The kernel does not share the evaluation of repeated subterms**, so emitted code passes literals and
  forces evaluation of shared values rather than re-computing them.
- **The kernel keeps every intermediate term of a declaration in memory**, so large checks are split into
  many small theorems, and many files, which a unifying file assembles.
- `native_decide` is never used, so Lean's compiler is never trusted.

## Checking that the theorems mean what they should

A green build means Lean accepted every proof. It does not mean the theorems say anything useful, or say
what you intended. The kernel cannot tell a meaningful theorem from a tautology, or the claim you meant
from a slightly weaker one that also compiles. Telperion has a layer of checks aimed at exactly these gaps.

- **Honesty lint** (`lean_lint`). Refuses `sorry`, `admit`, smuggled `axiom` declarations and decorative
  stubs such as `theorem foo : True := trivial`. It runs on every emitted file.
- **Non-vacuity** (`nonvacuity`). Refuses emitted theorems that are reflexive tautologies (`X = X`,
  `0 ≤ 0`). A companion registry (`emitter_sensitivity`) goes further for emitters whose proofs replay an
  identity: it corrupts the certificate and confirms the claim then fails, so the certificate is shown to
  be load-bearing.
- **Negative controls** (`negative_control`, `negative_control_harness`, `negctrl_adapters/`). These
  demonstrate the trust model instead of asserting it. For each emitter they bypass the Python
  self-check, forge a certificate of a *false* instance, emit it with the same code used for true
  instances, and confirm that the Lean kernel rejects it. They also check the positive half: a genuine
  certificate of a true instance must be accepted, so a harness that rejects everything cannot pass.
- **Statement match** (`statement_match`, `signature_gate`). Checks that a compiled theorem states the
  *intended* proposition, not a weaker one: it elaborates the intended statement against the emitted
  proof, so only a definitionally equal statement passes. `port_match` does the same when the two sides
  live in Lean projects with different toolchains.
- **Dual engines** (`faithfulness`). Cross-checks a primary implementation of a quantity against an
  independent one at seeded exact rational points, and refuses on any disagreement. Families can declare
  such an independent implementation directly.
- **An independent recheck** (`recheck`). Certificates can be exported to a JSON interchange format and
  re-verified by a deliberately separate code path that uses only the Python standard library (no sympy).
- **An auditor** (`audit`, `telperion audit`). Runs the same checks on Lean written by anyone else: a
  person, or an automated prover.
- **Self-application** (`self_hosting`, `metacircular`, `coverage`). Telperion certifies the hypotheses of
  its own reusable Lean lemmas, studies which part of its checking layer must itself be trusted, and
  profiles its own refusals to show which certificate shapes are missing.

## Independent verification with Comparator and nanoda

Telperion's own checks all run in Lean's kernel. For a second, independent opinion it produces challenges
for [Comparator](https://github.com/leanprover/comparator), the Lean FRO's tool for judging a proof
against a separately written statement. Given a *challenge* module (the statements, with `sorry`) and a
*solution* module (the proofs), Comparator:

1. builds both, inside the [landrun](https://github.com/Zouuup/landrun) sandbox;
2. exports both with `lean4export`;
3. checks that the solution proves **exactly** the challenge's statements, not something weaker;
4. checks that the proofs use only a whitelist of axioms (by default `propext`, `Quot.sound`,
   `Classical.choice`);
5. replays the proofs in Lean's kernel and, with `enable_nanoda`, in
   [nanoda](https://github.com/ammkrn/nanoda_lib), an independent implementation of the Lean kernel
   written in Rust.

A soundness bug would then have to fool two independently written kernels, and a mis-stated theorem
would have to match a statement written separately from the proof.

`telperion.comparator` builds the configuration from an emitted family:

```python
from telperion.comparator import challenge_for_result, write_challenge_config

config = challenge_for_result(result, profile, challenge_module="MyProject.Challenge")
write_challenge_config("comparator/demo.comparator.json", config)
```

which writes

```json
{
  "challenge_module": "MyProject.Challenge",
  "solution_module": "demo",
  "theorem_names": ["Demo.demo_nonneg_1", "Demo.demo_nonneg_2", "Demo.demo_nonneg_3"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": true
}
```

Then run `lake env comparator comparator/demo.comparator.json` in a project where Comparator is built.
Large emissions can be split into one configuration per shard. Some practical points:

- **Versions.** Build Comparator from the tag matching your Lean toolchain (for example `v4.32.0`).
  Its `lean4export` binary is built as a dependency and is found under
  `.lake/packages/lean4export/.lake/build/bin`; point `COMPARATOR_LEAN4EXPORT` at it, and
  `COMPARATOR_NANODA` at `nanoda_bin` (built with `cargo build --release` in `nanoda_lib`).
- **The sandbox.** landrun only runs on Linux. For your own proofs, a pass-through wrapper works; it must
  keep the `--` separator, because `lean4export` uses it and landrun's argument parser drops it. For
  proofs from anyone else, use a real sandbox.
- **Cost.** The nanoda replay is single-threaded and can take hours on proofs with large certificates.

The missions registry (below) uses the same bridge to judge its proved claims: it generates a challenge
from each claim's *registered* statement, independently of the file that proves it.

## Evolutionary certificate search (`telperion evolve`)

When the shape of a certificate is known but its ingredients are not, `telperion evolve` searches for them.
It runs an island-model MAP-Elites loop: several independent populations of candidate certificates
("genomes"), each kept in an archive of niches so that diverse candidates survive. Each generation, the best
candidate found so far is copied into every island. Each candidate is scored by

- an adversarial exact search that tries to **break** the claim (`hunt`, below);
- the exact certification tier it reaches (`certify`);
- and its complexity, so simpler certificates win ties.

Mutations come from three operators: *structured* ones, which are deterministic and need no model; *LLM*
ones, which ask a local language model through [Ollama](https://ollama.com) (default
`qwen2.5-coder:7b`) to propose new certificate ingredients; and a *hybrid* of the two.

```bash
telperion evolve --islands 4 --gens 20 --seed 0            # with a local Ollama model if one is running
telperion evolve --islands 4 --gens 20 --seed 0 --no-llm   # structured mutations only: deterministic in the seed
```

The measurement harness (`evolve/measure.py`) compares the two modes over many trials: how often the
champion certifies, how many evaluations it takes, and whether the model invented anything outside the
built-in pool. `evolve/freeze.py` turns a champion into Lean through the ordinary emitters, and
`evolve/kernel.py` builds it against a Lean project.

The search changes nothing about trust. It only *proposes*; a champion becomes a theorem only by passing
the same certify, emit and kernel gate as everything else, and nothing it finds is frozen automatically.
The current genome encodes one certificate family (unimodal-ratio certificates, where the maximum of a
sequence sits at its up-to-down crossing), and the loop is built so other genomes can be added.

## Working with AI provers and agents

Telperion is designed to be a *deterministic backend* for probabilistic provers: a language model can
propose, and Telperion certifies or refuses in exact arithmetic.

- **One goal at a time** (`prove.prove_goal`). Takes a single claim `0 ≤ target` over nonnegative
  variables and returns either a complete, self-contained Lean theorem, or a triage: *false* (with an
  exact rational counterexample), *true but not in this certificate form*, or *certifiable but set up
  wrongly*. It tries Pólya certificates first, then sums of squares.
- **From words to a statement** (`formalize`). A language model turns an informal claim into a candidate
  formal goal. It only proposes the *statement*; the deterministic core then certifies or rejects it, so
  a wrong translation cannot produce a false theorem. As always, a human should still read the statement.
- **Filling gaps** (`gap_fill`). Given a Lean file in which an analytic step is a lemma proved by `sorry`,
  it extracts the goal, recognizes its certificate shape, generates the proof, and re-verifies it, with an
  automatic repair pass for Mathlib renames. An experimental warm Lean worker (`lean_server`, off unless
  configured) keeps a Lean process running so that repeated checks can take under a second.
- **Measuring the benefit** (`backend_lift`). A harness that measures how many goals an LLM prover
  solves with Telperion as a backend that it misses alone.
- **An MCP server** (`telperion-mcp`, with the `mcp` extra). Exposes the certify, validate and emit
  workflow as tools for AI agents such as Claude Code (`claude mcp add telperion -- telperion-mcp`). There
  is deliberately no tool that emits without certifying and validating first.

## Probing a claim before proving it

Much of the work in a computer-assisted proof happens before any certificate exists: deciding whether a
claim is true, where it is tight, and whether a certificate of a given kind can possibly work. These probes
answer such questions exactly.

- **`diagnose`**: when certification fails, separates "false" from "true but not in this form" from "set
  up wrongly", and suggests transformations.
- **`hunt`**: an adversarial exact minimizer that tries hard to *break* a claim, over the orthant or a
  box, before anyone tries to prove it.
- **`relax`**: relaxes an integer parameter to a continuous one. If the relaxed claim fails, no smooth
  certificate can prove the original, and the proof must use integrality.
- **`probe_sharp`**: finds where the *certificate* stops working and where the *claim* stops being true,
  and reports the gap between them.
- **`margins`**: finds exactly where a family is tight (its equality cases) and by how much it holds
  elsewhere.
- **`upgradability`**, **`circularity`**, **`super_solution`**: tell a finite check that really covers
  every case from a sample that only probes an unbounded one; refuse a "lemma" that already implies the
  goal it is meant to reduce to; and test Bellman-style super-solutions exactly.
- **`verdict`**, **`ledger`**: close every probe with one of four explicit verdicts, and keep an
  append-only record of dead ends with their refutations, so failed routes are not retried.
- **`cilog`**: a catalogue of Lean build failures and their known repairs, matched against a build log.

## More certificate finders

Beyond the emitters' own certifiers, three standalone finders search for certificates the simpler
methods cannot find:

- **`sos_sdp`**: sums-of-squares certificates found by semidefinite programming (with the `sdp` extra),
  then rounded to exact rationals and checked exactly.
- **`psd`**: exact positive-semidefiniteness certificates by a square-root-free Cholesky factorization,
  with no floating point at all.
- **`sonc`**: sums of nonnegative circuit polynomials, an AM–GM-based certificate that covers some
  polynomials sums of squares cannot.

## Managing a project

- **`telperion init`**: scaffolds a new project: a family template with validation built in, a Lean
  project pinned to a known-good toolchain, and a GitHub Actions workflow that compiles the emitted Lean.
- **`telperion status`**: generates a status report by *running* the project's checks, so a claim in the
  report cannot outrun its verification; `review-brief` produces a checklist for a skeptical reviewer.
- **`telperion latex`**: renders a certified family as a paper appendix stamped with the *same* input hash
  as the Lean files, so a reader can confirm the paper and the formalization match by comparing two
  strings.
- **Maintenance**: a proof-repair pass for Mathlib renames, driven by Mathlib's own deprecation records;
  a content-addressed index of emitted statements that finds the same lemma proved under two names; a
  merger that combines emitted files and refuses name clashes between different statements; per-theorem
  dependency extraction, for re-checking exactly what a change touches; and a certification cache that is
  a speed layer only.
- **`telperion verify`**: elaborates Lean against a pre-built project and reports its axioms, in one call.

## The missions registry

For long campaigns with many interlocking claims, `telperion mission` keeps a registry: a graph of
mathematical statements, each a node with a status (draft, open, proved, refuted or deprecated) and
dependencies on other nodes.

- **Only a verification gate can mark a node proved or refuted.** It checks that a compiled Lean artifact
  contains the node's registered statement, is free of `sorry`, and is actually built by CI (a file that
  nothing compiles proves nothing), and it propagates results through the graph.
- **Statements are separate from proofs.** Each node's statement is rendered into its own Lean file with
  a hash in its header, so hand edits are detected, and definitions copied into proof projects are checked
  for drift against the registry's originals.
- **Provenance.** The registry records who wrote each statement and who read it back to confirm it says
  what its title claims. That reading is the one link no machine checks, so the registry makes
  self-certification visible and refuses a readback by the statement's own author. (Identities are
  self-reported, so this guards against mistakes rather than against deliberate deception.)
- **An independent judge.** Proved nodes can be re-checked by Comparator against their registered
  statements.
- **Coordination.** Sessions claim nodes with an expiring lock, and every attempt (proved, refuted, no-go
  or stalled) goes into an append-only log.

## Connecting to the wider world

These modules make network requests, but only when you invoke them, and nothing they bring in is trusted:
it all goes through the same certify, emit and kernel gate.

- **Source mining** (`telperion source-mine`, `telperion palomar-mine`). Watches public sources for results
  whose certificate shapes Telperion can emit: the [Palomar](https://palomar-registry.org) registry of
  verified formalizations, commits to Lean mathematics libraries on GitHub, formalization repositories
  that publish Comparator challenges, and (read-only) discussion on the Lean Zulip. Each hit becomes a
  *lead*: a port of something already formalized, or a candidate to formalize.
- **External proof platforms** (`telperion p2m`). A client for [prove2.me](https://prove2.me) that triages
  its problems by certificate shape and submits attempts. The client enforces its own safety rules: a
  protocol-version check, throttling, backoff, and a circuit breaker that stops all requests after repeated
  server errors. Credentials live outside the repository.

## Installation

Python 3.11 or later. From this directory:

```bash
pip install -e .                 # the core engine: needs only sympy
pip install -e ".[dev]"          # with the test dependencies
pip install -e ".[flint]"        # ball-arithmetic enclosures (python-flint)
pip install -e ".[sdp]"          # semidefinite-programming search for SOS certificates (cvxpy)
pip install -e ".[mcp]"          # the MCP server
```

Emitted Lean needs a Lean 4 project with Mathlib. Telperion is tested against the Lean and Mathlib
versions pinned by the project it is used in; here, Lean 4 v4.32.0 and Mathlib v4.32.0.

## About this copy

This directory is a vendored snapshot (version 0.1.6, engine source synced 2026-10-01) of the complete engine source,
including every emitter, taken from the separate repository where Telperion is developed. It differs from
the development version only in a handful of comments and docstrings, which were reworded to remove
references to unrelated private projects; no code or mathematics was changed. The tests, examples and documents below were synced on
2026-09-27 and do not yet include the tests of the newest emitters.

Alongside the source it carries most of the development repository's supporting material:

- `tests/`: the test suite, about 3,000 tests. Run it with `pip install -e ".[dev,sdp,rh_jensen]"` and then
  `python -m pytest` from this directory; CI does the same on every change (`.github/workflows/telperion.yml`).
  Some tests need files that live only in the development repository (its missions registry, repository
  scripts and Lean projects). Twelve modules that cannot load without them are left out, and about a hundred
  individual tests are skipped with a stated reason; `tests/conftest.py` lists them all.
- `examples/`: 22 small worked examples, one or a few per certificate shape, each small enough to read in a
  sitting.
- `docs/`: design notes and references: architecture, the trust boundary (`TRUSTED_FLOOR.md`), the tactic
  contract, Comparator, the missions registry, the honesty patterns, and the emitter catalogues and status
  notes from the Riemann-hypothesis work. A few links in them point at files that are not published here;
  those are left as plain text.
- `CHANGELOG.md` and `CONTRIBUTING.md`.

The project site also hosts the [Telperion registry explorer](https://drmurphyisin.github.io/brualdi-goldwasser/telperion-explorer/),
a page generated from the development repository's missions registry, with a Brualdi-Goldwasser tab in
front. The page was last regenerated from the registry on 2026-10-01. The registry's `bg` campaign has not
changed since 2026-09-24, two days before the final theorem; the page says so.

The subpackage `telperion.bg` is a research lab of probes specific to the Brualdi–Goldwasser problem. It is
not part of the engine: the engine never imports it, and the development repository enforces that
boundary with a test.

In this repository, the Brualdi–Goldwasser certificate generators are standalone scripts (in
`../certificates/`). They use Telperion's provenance layer (`EmitResult`, `freeze`, `diff_frozen`) to
record every certificate family and to check that it regenerates byte for byte.

## All emitters

<!-- EMITTERS:BEGIN -->
All 169 emitter modules in `src/telperion/`, in alphabetical order. The *kind* is the name an
emitter registers under (a module may register several); the summary is the first sentence of the
module's own docstring, so it uses the development repository's vocabulary. Generated by
`scripts/gen_emitter_list.py`.

| module | kind | summary |
|---|---|---|
| `emit.py` | `bilinear_box`, `direct_polya` | Kind-1 emitters: certificate batches (direct Polya and bilinear box). |
| `emit_achievability.py` | `achievability` | Achievability-closure emitter — replace a relaxed inequality that is FALSE on its full (relaxed) domain by its restriction to the *achievable* subset, where it holds. |
| `emit_adapters.py` | `case_dispatch_assembly`, `custom_assembly`, `reparam_adapter`, `subdivision_glue` | Kind-2 and Kind-3 emitters: reparameterization adapters and case-dispatch assemblies. |
| `emit_admissible_tuple.py` | `admissible_tuple` | AdmissibleTuple emitter (kind `admissible_tuple`) — the prime-gaps admissible k-tuple certificate, distilled from the `bgp212` Lemma 12.1 shape (the 45-tuple H45 is admissible with diameter 212). |
| `emit_affine_hull_dominance.py` | `affine_hull_dominance` | affine_hull_dominance emitter -- the EXACT MAXIMUM, over all finite trees on n vertices, of a quantity computed by a POSITIVE MULTILINEAR tree recursion, certified by convex-hull pruning with explicit convex-combination domination witnes… |
| `emit_affine_param_endpoint.py` | `affine_param_endpoint` | BG SCLStep "affine-in-parameter endpoint" emitter — the price-interval collapse. |
| `emit_algebraic_bracket.py` | `algebraic_bracket` | Algebraic-bracket emitter: rigorous rational two-sided enclosures of a square root. |
| `emit_anchored_monotone_extension.py` | `anchored_monotone_extension` | anchored_monotone_extension emitter -- a normalized parametric tree recursion is antitone past a threshold, so an anchor value bounds the whole half-line. |
| `emit_annulus_count.py` | `annulus_count` | Annulus-count emitter — zeros in a shell via `∮_{C(c,R)} − ∮_{C(c,r)} = 2πi · Σ_shell m`. |
| `emit_argument_principle.py` | `argument_principle` | Argument-principle emitter — the winding/residue bridge `∮ Σ m/(z−ρ) = 2πi · Σ m`. |
| `emit_autocorr_support.py` | `autocorr_support` | AutocorrSupport emitter (kind `autocorr_support`) — the support-geometry autocorrelation bound, ported from anthropics/zeta-23-lean `Taper/Decay.lean` (`autocorr_le_of_support`). |
| `emit_baez_duarte.py` | `baez_duarte` | Báez-Duarte emitter — Face 6 (spectral / approximation) of the RH obstruction. |
| `emit_bagchi_recurrence.py` | `bagchi_recurrence` | Bagchi-recurrence emitter — Face 4 (recurrence) of the RH obstruction. |
| `emit_bc_deriv_re.py` | `bc_deriv_re` | Real-part → derivative bound emitter — the Borel-Caratheodory + Cauchy engine. |
| `emit_bc_split.py` | `bc_split` | BC-split emitter — the log-derivative "split + entire bound" combine, as a kernel-checked Lean certificate. |
| `emit_bernstein.py` | `bernstein` | Bernstein-basis positivity emitter — `0 ≤ p(x)` on a closed interval `[a, b]` via nonnegative Bernstein coefficients. |
| `emit_bilinear_corner.py` | `bilinear_corner` | Bilinear-corner box-positivity emitter — worst-corner positivity of a bilinear form on an axis-aligned box. |
| `emit_borel_caratheodory.py` | — | Borel–Carathéodory bound — packaging the (now UPSTREAM) Mathlib theorem. |
| `emit_box_localization.py` | `box_localization` | Box-localization emitter — RH-in-a-box capstone counting step (Stage 3). |
| `emit_box_residue_sum.py` | `box_residue_sum` | Box residue-sum emitter — the box analogue of full_argument_principle (conditional on winding). |
| `emit_box_robust.py` | `box_robust` | Box-robust kernel emitter (#2): forall-box separable-quadratic nonnegativity. |
| `emit_bracket.py` | `bracket` | Interval-bracket emitter: rigorous rational enclosures of transcendental constants. |
| `emit_bragg_amplitude.py` | `bragg_amplitude` | Bragg-amplitude emitter — a certified truncated diffraction (trig) sum over bracketed ordinates. |
| `emit_bragg_floor.py` | `bragg_floor` | Bragg-floor emitter — Route P Brick D3 part 2 (the Dyson-quasicrystal diffraction certificate). |
| `emit_cauchy_deriv.py` | `cauchy_deriv` | Cauchy derivative-estimate emitter — a reusable wrapper for Cauchy's bound on a disk. |
| `emit_cavity_exchange.py` | `cavity_exchange` | BG Kelmans de-branch monotonicity emitter — "cavity exchange" corner reduction. |
| `emit_cg_round.py` | `cg_round` | Chvatal-Gomory integer-rounding emitter (VIPR-style) -- a linear goal over INTEGER variables, derived by nonnegative combination + integer rounding. |
| `emit_coefficient_mass.py` | `coefficient_mass` | CoefficientMassEval emitter — the ℓ¹-coefficient sup-envelope distilled from the OpenAI Navier--Stokes blowup formalization (`github.com/openai/NavierStokesAndEuler`, `NavierStokes/EdgeWeightJets.lean` `polynomial_eval_bound`, Apache-2.0… |
| `emit_comparability_envelope.py` | `comparability_envelope` | ComparabilityEnvelope emitter — three comparability/Lipschitz atoms distilled from the OpenAI Navier--Stokes blowup formalization (`github.com/openai/NavierStokesAndEuler`, Apache-2.0; `NavierStokes/PhysicalGraphBounds.lean` `comparable_… |
| `emit_complex_re_im_split.py` | `complex_re_im_split` | complex_re_im_split emitter -- kernel-checked REAL / IMAGINARY-PART SPLITS of a complex polynomial expression, plus the two norm faces they feed and the cast face of a real-valued one. |
| `emit_concave_pooled_induction.py` | `concave_pooled_induction` | concave_pooled_induction emitter -- a bound on a BRANCHING (tree) recursion, certified by a CONCAVE one-scalar witness checked at the POOLED MEAN of the children's messages. |
| `emit_concave_stationary_max.py` | `concave_stationary_max` | Concave-stationary-max emitter — a stationary point of a strictly concave objective is its unique maximizer. |
| `emit_cone.py` | `cone` | Cone / Farkas emitter — target as a nonnegative combination of a basis. |
| `emit_consequence.py` | `consequence` | Equational-consequence emitter — an equation that FOLLOWS from polynomial equation hypotheses. |
| `emit_constrained_sos.py` | `putinar` | Constrained SOS / Putinar-Positivstellensatz emitter — nonnegativity of a polynomial ON a basic closed semialgebraic set `{g_1 ≥ 0, …, g_m ≥ 0}`. |
| `emit_continuous_barrier.py` | `continuous_barrier` | ContinuousBarrierBootstrap emitter — the open-closed continuity bootstrap distilled from the OpenAI Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, `Euler/GevreyFlowBootstrap.lean` `continuous_barrier`, Apache-2.0;… |
| `emit_cs.py` | `cauchy_schwarz` | Cauchy–Schwarz / QM–AM emitter — a pairwise-difference SOS symmetric inequality. |
| `emit_curvature_boundary.py` | `curvature_boundary` | Curvature-boundary "extremum-on-the-boundary" emitter — the sign-definite-f'' face. |
| `emit_defect_witness.py` | `defect_witness` | Defect-witness emitter — the two-configuration inertia gap (MIRRORMERE QC-B3). |
| `emit_dirichlet_repr.py` | — | Euler-Maclaurin / Abel-summation representation emitter (zeta-type Dirichlet series). |
| `emit_discrete_moment.py` | `discrete_moment` | DiscreteMoment emitter — discrete-sum moment atoms distilled from the OpenAI Navier--Stokes/Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, Apache-2.0; `Euler/GevreyInversePartitions.lean` `sum_partSize_sq_le`, `Nav… |
| `emit_disjoint_discs.py` | `disjoint_discs` | Disjoint-discs emitter -- the CONCRETE-INSTANCE shape of the MIRRORMERE E4b isolation lemma. |
| `emit_disk_coord.py` | `disk_coord` | Disk -> coordinate-bounds emitter (Farkas-style linear coordinate certificate). |
| `emit_domain_to_orthant.py` | — | Constrained-domain positivity via an affine map to the nonnegative orthant. |
| `emit_dominated_integrability.py` | — | Dominated-integrability emitter (integrable-by-rpow-domination). |
| `emit_domination_ratio.py` | `domination_ratio` | Rational domination-ratio emitter — a template dominates a competitor via an all-nonneg-coefficient rational ratio `r(params) = P/Q ≥ 1` on a parameter box. |
| `emit_enclosure_fold.py` | `enclosure_interval_fold` | EnclosureIntervalFold emitter (kind `enclosure_interval_fold`) — the integer near-CUE row-band checker, distilled from the `anthropics/zeta-23-lean` PairCeiling development (`NumericCert.lean` / `RowCert.lean`). |
| `emit_enclosure_tree.py` | `enclosure_tree` | enclosure_tree emitter -- kernel-checked RATIONAL TWO-SIDED ENCLOSURES of an expression TREE over transcendental and algebraic atoms. |
| `emit_endpoint_geom_cap.py` | `endpoint_geom_cap` | Endpoint geometric-factor cap emitter — the entire-part factor is maximised at the endpoint. |
| `emit_entire_part_bound.py` | `entire_part_bound` | Entire-part bound emitter — ‖logDeriv g c‖ bounded by the oscillation of log‖g‖. |
| `emit_eventual_threshold.py` | `eventual_threshold` | EventualScalingThreshold emitter — "holds for all sufficiently large scale" with a computed max-of-ratios witness, distilled from the OpenAI Navier--Stokes blowup formalization (`github.com/openai/NavierStokesAndEuler`, `NavierStokes/Con… |
| `emit_exp_enclosure.py` | `exp_enclosure` | exp-enclosure emitter -- kernel-checked RATIONAL BRACKETS of `Real.exp` (and of the recurrence deficit `e^d + e^-d - 2` and `Real.cosh`) from Mathlib's `Real.exp_bound`. |
| `emit_exp_laurent_identity.py` | `exp_laurent_identity` | ExpLaurentIdentity emitter -- identities in `Real.exp d` and `Real.exp (-d)` certified as an exact reduction modulo the SINGLE relation `e^d * e^(-d) = 1`. |
| `emit_exp_threshold.py` | `exp_threshold` | exp_threshold emitter -- from a threshold on the Gaussian width to exponential domination, by the one-line discipline `1 + t <= e^t` (Mathlib's `Real.add_one_le_exp`). |
| `emit_factored_endpoint_enclosure.py` | `factored_endpoint_enclosure` | factored_endpoint_enclosure emitter -- an inequality `F >= 0` on closed boxes that TOUCH a singular endpoint, by factoring out the vanishing power and checking the cofactor's sign. |
| `emit_facts.py` | `exact_fact`, `identity` | IdentityEmitter and ExactFactEmitter: the equality half of a campaign. |
| `emit_far_pole_sum.py` | `far_pole_sum` | Far-pole sum emitter — a sum of rational terms whose poles lie OUTSIDE the disk is bounded. |
| `emit_finite_argmax.py` | `finite_argmax` | Finite-argmax margin emitter: a designated winner strictly beats a finite list of competitors, certified by cross-multiplied INTEGER strict inequalities. |
| `emit_finite_decide.py` | `finite_decide` | Finite-decide certificate emitter — guarded ∀-facts over explicit tables, proven in Lean by kernel `decide`. |
| `emit_finite_prefix_absorption.py` | `finite_prefix_absorption` | FinitePrefixAbsorption emitter — "eventually bounded ⟹ globally bounded, with an explicit constant" distilled from the OpenAI Navier--Stokes blowup formalization (`github.com/openai/NavierStokesAndEuler`, `NavierStokes/GaugeAliasDecay.le… |
| `emit_full_argument_principle.py` | `full_argument_principle` | Full argument-principle emitter — residue-sum PLUS analytic-vanishing in one theorem. |
| `emit_fwd_telescope.py` | `fwd_telescope` | Forward-difference telescoping emitter — the W2 prover, mechanizing the SumEqProd.lean template (2026-08-20, knapsack_sos arc). |
| `emit_gap_budget_multiplicity.py` | `gap_budget_multiplicity` | gap_budget_multiplicity emitter -- pruning a multiset optimisation by a tangent-price GAP BUDGET, with every step checked by the Lean kernel. |
| `emit_gevrey_majorant.py` | `gevrey_majorant` | GevreyFactorialMajorant emitter — the Gevrey-2 majorant calculus distilled from the OpenAI Euler finite-time-blowup formalization (`github.com/openai/NavierStokesAndEuler`, `Euler/EulerProof.lean`, Apache-2.0; lemma chain `le_choose_of_i… |
| `emit_graded_convolution.py` | `graded_convolution` | GradedConvolutionEndpoint emitter — exact identity calculus on truncated antidiagonal convolutions, distilled from the OpenAI Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, `Euler/FiniteGradeTriangular.lean` / `Fin… |
| `emit_grid_modulus_nonvanishing.py` | `grid_modulus_nonvanishing` | Grid-modulus non-vanishing emitter — a Lipschitz-net zero-freeness certificate. |
| `emit_halfplane_disk.py` | `halfplane_disk` | Half-plane -> disk positivity emitter (Borel-Caratheodory / Moebius-Schwarz core). |
| `emit_handelman.py` | `handelman` | Handelman-Positivstellensatz emitter — nonnegativity of a polynomial on a POLYTOPE `{ℓ_1 ≥ 0, …, ℓ_m ≥ 0}` via a nonnegative combination of PRODUCTS of the defining linear forms. |
| `emit_herglotz_lower.py` | `herglotz_lower` | Herglotz lower-bound emitter — keep the equal-height zero, drop the nonnegative rest. |
| `emit_hermitian_moment.py` | `rank_trace_scalar`, `two_moment_count` | HermitianMomentInertia emitter family — certificate shapes ported from the Anthropic `zeta-23-lean` development (arXiv:2608.13637, *"More than two thirds of the zeros of ζ lie on the critical line"*, author: a Claude model). |
| `emit_hyperbolicity.py` | `hyperbolicity` | Hyperbolicity emitter (#3, d=2): real-rootedness of a quadratic over a box. |
| `emit_infeasible.py` | `infeasible` | Infeasibility / Nullstellensatz-refutation emitter — a polynomial system has NO solution. |
| `emit_integrality_gate.py` | `integrality_gate` | Integrality-gate emitter — a finite exceptional table + a uniform p-adic valuation certificate (the BG "23-gate" strictness). |
| `emit_interlacing.py` | `interlacing` | Interlacing / real-rootedness emitter — Newton log-concavity of coefficients. |
| `emit_interval_gram_inertia.py` | `interval_gram_inertia` | Interval-Gram-inertia emitter -- kernel-certified inertia (posIndex, defect) of EVERY Hermitian matrix inside a rational interval box. |
| `emit_jensen_polynomial_hyperbolicity.py` | `jensen_polynomial_hyperbolicity` | JensenPolynomialHyperbolicityEmitter: d=2 box hyperbolicity, compile-gated. |
| `emit_jensen_zero_count.py` | `jensen_zero_count` | Jensen zero-count emitter — bound the number of zeros of an analytic function in a disk by its boundary growth, as a kernel-checked Lean certificate. |
| `emit_lattice_box.py` | `lattice_box` | Lattice-box emitter — the d-dimensional integer Positivstellensatz shape. |
| `emit_leakage_dictionary.py` | `leakage_dictionary` | leakage_dictionary emitter -- the log-derivative coefficient functional at a COMPOSITE index. |
| `emit_lee_yang.py` | `lee_yang_stable_pair` | LeeYangStablePair emitter — Schur stability of a rational-coefficient polynomial, the finite-checkable core of the Dyson-quasicrystal / Kurasov–Sarnak "zeros on a line by construction" analogue. |
| `emit_lehmer_pair.py` | `lehmer_pair` | Lehmer-pair emitter — Face 5 (deformation / criticality) of the RH obstruction. |
| `emit_lfunction_product.py` | `lfunction_product` | L-function product lower-bound emitter: the nonneg-cosine -> 3-4-1 product bound. |
| `emit_li_positivity.py` | `li_positivity` | Li positivity-ladder emitter — the RH-roadmap Track-2 showcase. |
| `emit_log_combination.py` | `log_combination` | Log-combination emitter — the "F*-folding" companion to `transcendental_enclosure`. |
| `emit_log_eps_optimize.py` | `log_eps_optimize` | LogEpsilonWitnessOptimization emitter — the cutoff-parameter optimization distilled from the OpenAI Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, `Euler/LogarithmicCutoffOptimization.lean` `optimize`, Apache-2.0). |
| `emit_log_product_bound.py` | `log_product_bound` | Log-product boundary-bound emitter — the zero-factor magnitude bound (dVP two-scale). |
| `emit_logconcave.py` | `logconcave` | Log-concave single-point reduction emitter. |
| `emit_logconvex_interp.py` | `logconvex_interp` | LogConvexEndpointProduct emitter — zero-tolerant log-convexity interpolation distilled from the OpenAI Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, `Euler/NonnegativeLogConvex.lean`, Apache-2.0). |
| `emit_logderiv_region.py` | `logderiv_region` | de la Vallee Poussin log-derivative region-core emitter. |
| `emit_low_order_tail.py` | `low_order_tail` | LowOrderGeometricTail emitter — hybrid finite-low-grades + doubled geometric tail certificate, distilled from the OpenAI Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, `Euler/PacketFiniteSumBounds.lean` `weighted_l… |
| `emit_magnitude_split.py` | `magnitude_split` | Magnitude-split triangle-inequality emitter — a three-term `A + B - C` norm bound assembled from per-term magnitude bounds. |
| `emit_max_modulus.py` | `max_modulus` | Maximum-modulus propagation emitter — a sphere norm bound propagates to the disk. |
| `emit_mobius_tangent_cell.py` | `mobius_tangent_cell` | mobius_tangent_cell emitter -- a search-free TWO-EVALUATION certificate for one-variable inequalities "linear + concave logs + one Mobius term <= 0" on a rational interval. |
| `emit_monomial_ladder.py` | `monomial_ladder` | MonomialBudgetLadder emitter — one master smallness budget absorbing a family of monomial rung obligations, distilled from the OpenAI Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, `Euler/PacketGeometryGuards.lean`… |
| `emit_monotone_tail.py` | `monotone_tail` | Monotone-ratio family-tail emitter — the `b(s) <= B for all s >= s0` shape. |
| `emit_mt_cosine.py` | — | Mossinghoff–Trudgian-style OPTIMAL nonnegative-cosine polynomials, with an exact, search-free Fejér–Riesz sum-of-squares certificate. |
| `emit_multilinear_perturbation.py` | `multilinear_perturbation` | MultilinearProductPerturbation emitter — the Leibniz telescoping first-order comparison distilled from the OpenAI Navier--Stokes blowup formalization (`github.com/openai/NavierStokesAndEuler`, `NavierStokes/MovingFrameODE.lean` `product_… |
| `emit_nonneg_orthant.py` | — | Nonneg-orthant positivity certificates: `p(v) > 0` for `v ≥ 0` when `p` has all-nonnegative coefficients and a strictly positive constant term. |
| `emit_ns_ledger.py` | `affine_ledger` | AffineLedger emitter family — distilled from the OpenAI Navier--Stokes / Euler formalization (`github.com/openai/NavierStokesAndEuler`, `NavierStokes/ExponentLedger.lean`, manuscript Proposition 10.3). |
| `emit_nullstellensatz.py` | `nullstellensatz` | Nullstellensatz / ideal-membership emitter — a polynomial VANISHES on the variety of an ideal, certified by explicit cofactors. |
| `emit_order_balance.py` | `order_balance` | Order-balance boundary-contradiction emitter (the integer zero/pole-order hinge at the 1-line, `ζ(1+it) ≠ 0`). |
| `emit_order_residue.py` | — | Order = residue of the logarithmic derivative — packaging the proven `residue_logDeriv`. |
| `emit_padic.py` | `valuation` | p-adic valuation emitter — first-class Tier-1 arm. |
| `emit_parametric_holomorphy.py` | `parametric_holomorphy` | Parametric-holomorphy emitter — analyticity of a parametric tail integral. |
| `emit_partition_composition.py` | `partition_composition` | GevreyPartitionComposition emitter — the Faà di Bruno factorial-square partition bound, ported verbatim from the OpenAI Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, `Euler/GevreyCompositionPartitions.lean`, Apach… |
| `emit_pe_duality.py` | `pe_duality` | Pseudo-expectation / SoS-duality emitter — "no degree-d SoS refutation exists". |
| `emit_per_size_dominance_sweep.py` | `per_size_dominance_sweep` | BG per-size domination sweep emitter (Hdom) — a FINITE per-n sweep of configs. |
| `emit_poly_exp_absorption.py` | `poly_exp_absorption` | PolyExpAbsorption emitter — inverse-power prefactors absorbed into a halved exponential rate, distilled from the OpenAI Navier--Stokes blowup formalization (`github.com/openai/NavierStokesAndEuler`, `NavierStokes/OutgoingPulseBounds.lean… |
| `emit_poly_geom_closure.py` | `poly_geom_closure` | PolynomialWeightedGeometricClosure emitter — exact-invariant uniform bounds for polynomially-weighted geometric series, distilled from the OpenAI Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, `Euler/PacketFieldSob… |
| `emit_polya_zeros.py` | `polya_zeros` | Pólya-with-zeros emitter — homogeneous Pólya certificates that TOLERATE zeros on faces (Castle–Powers–Reznick 2011, "Pólya's theorem with zeros", J. |
| `emit_polytope_max.py` | `polytope_max` | Polytope-max (multi-affine corner) box-positivity emitter — the general-d generalization of the shipped bilinear-corner emitter ("Handelman Route B": corner dispatch + per-edge affine slice). |
| `emit_polytope_moment.py` | `polytope_moment` | PolytopeMoment emitter — exact-rational simplex-moment certificates, the shape of Axiom Math's `bgp212` development (the *"H1 ≤ 212"* paper), Lemma 10.1 / identity (10.1). |
| `emit_power_tower.py` | `power_tower` | PowerTowerRecurrenceClosure emitter — polynomial self-composition recursions closed to a doubly-exponential tower normal form, distilled from the OpenAI Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, `Euler/H6Press… |
| `emit_preconnected_cover.py` | — | Preconnectedness-by-convex-cover emitter. |
| `emit_preordering_multiplier.py` | `preordering_multiplier` | Preordering-with-multiplier emitter -- kernel-checked nonnegativity of a polynomial on a semialgebraic set cut out by POLYNOMIAL generators, via a positive multiplier and a constant-coefficient (Schmuedgen preordering) identity. |
| `emit_primality.py` | — | Primality emitter — a Pratt/Lucas certificate discharged through Mathlib's `lucas_primality`. |
| `emit_psd_form.py` | `psd_form` | Positive-definite quadratic-form emitter — a deterministic, cvxpy-free PSD certificate via exact rational LDLᵀ congruence. |
| `emit_quadratic_irrational.py` | `quadratic_irrational` | QuadraticIrrationalSeparation emitter — distilled from the OpenAI Navier--Stokes formalization (`github.com/openai/NavierStokesAndEuler`, `NavierStokes/DiophantineGraph.lean`). |
| `emit_ratio_telescope.py` | `ratio_telescope` | RatioRecurrenceTelescope emitter — multiplicative telescoping of per-step ratio bounds into closed normal forms, distilled from the OpenAI Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, Apache-2.0; `Euler/GevreyInv… |
| `emit_rational_identity.py` | `rational_identity` | Rational-function identity emitter — `lhs = rhs` over ℚ on a ray. |
| `emit_rational_sos.py` | `rational_sos` | Rational-SOS (Artin / Reznick denominator) emitter — `0 ≤ p` for a polynomial that is nonnegative but NOT a sum of squares. |
| `emit_rayleigh_gram.py` | `rayleigh_gram` | RayleighGram emitter — a concrete-instance shadow of the generalized-eigenvalue / Rayleigh-quotient lower bound from Axiom Math `bgp212` Theorem 11.1 (the "H₁ ≤ 212" development). |
| `emit_real_nullstellensatz.py` | `real_nullstellensatz` | Real-Nullstellensatz emitter — a polynomial vanishes on the REAL variety of an ideal. |
| `emit_rect_argument_principle.py` | `rect_argument_principle` | Rectangle argument-principle emitter — Cauchy vanishing on a box boundary `∮_{∂rect} E = 0`. |
| `emit_rect_winding.py` | `rect_winding` | Rectangle winding-number emitter — the winding-NONZERO primitive, from scratch. |
| `emit_recursion_closure.py` | `recursion_closure` | BG per-hub SCL node-decouple "recursion closure" emitter. |
| `emit_reexport.py` | — | Re-export emitter — wrap an already-proven / upstream Lean theorem as a named lemma. |
| `emit_reflection_halving.py` | `reflection_halving` | ReflectionHalving emitter (kind `reflection_halving`) — the finite instance of the reflection / functional-equation halving bound |
| `emit_regular_word.py` | `regular_word` | RegularWordLinearInvariant emitter — a linear counting invariant over a forbidden-factor word grammar, distilled from the OpenAI Navier--Stokes blowup formalization (`github.com/openai/NavierStokesAndEuler`, `NavierStokes/VolterraAnalyti… |
| `emit_robin_growth.py` | `robin_growth` | Robin-growth emitter — Face 2 (temperedness) of the RH obstruction. |
| `emit_rpow_budget.py` | `rpow_budget` | RpowExponentBudget emitter — k-power product collapse with exponent-level `linarith`, distilled from the OpenAI Euler blowup formalization (`github.com/openai/NavierStokesAndEuler`, `Euler/PacketExponentialTail.lean` `normalized_tail_exp… |
| `emit_scale_invariance.py` | `scale_invariance` | Scale-invariance / objective-degeneracy emitter — a homogeneity certificate. |
| `emit_second_order.py` | `second_order` | Second-order linear-recurrence closed-form emitter — the three-term generalization of the first-order forward telescoping emitter (`emit_fwd_telescope.py`, the W2 prover mechanizing SumEqProd.lean). |
| `emit_selfinversive_rigidity.py` | `selfinversive_rigidity` | Self-inversive rigidity emitter — equal-modulus real-rootedness (MIRRORMERE R3, n=2). |
| `emit_separable_convex.py` | `separable_convex` | Separable-convex extremum emitter — the extremum of a separable convex sum on a fixed-sum box is at the homogeneous point (MIN) or a vertex (MAX). |
| `emit_single_crossing_ladder.py` | `single_crossing_ladder` | single_crossing_ladder emitter -- single crossing of consecutive members of a parametric family, increasing breakpoints, and the resulting best-member ladder. |
| `emit_slit_loop_winding_zero.py` | `slit_loop_winding_zero` | Slit-loop winding-zero emitter — the homotopy-free heart of Rouché. |
| `emit_sos.py` | `sos`, `sos_sdp` | First-class SOS/SDP emitter — the LP -> SDP upgrade of the certifier. |
| `emit_sos_refutation.py` | `sos_refutation` | SOS-Positivstellensatz refutation emitter — a semialgebraic system is unsatisfiable OVER ℝ, closing the real-only gap the ideal-theoretic refutation (`InfeasibilityEmitter`) leaves open. |
| `emit_spacing_tail.py` | `spacing_tail_bound` | SpacingTailBound emitter — a concrete-instance shadow of the uniform spacing tail bound from `anthropics/zeta-23-lean` (`MV/Spacing.lean`, `spacing_sq` / `spacing_four`). |
| `emit_spectral_factorization.py` | — | Fejér–Riesz spectral factorization: ANY nonnegative trig polynomial → exact SOS. |
| `emit_sphere_bound.py` | `sphere_bound` | Sphere-bound emitter — turn a strip-type pointwise growth bound into a UNIFORM bound on a sphere, as a kernel-checked Lean certificate. |
| `emit_sqrt_root_elimination.py` | `sqrt_root_elimination` | SqrtRootElimination emitter — symbolic radical elimination distilled from the OpenAI Navier--Stokes formalization (`github.com/openai/NavierStokesAndEuler`, `NavierStokes/ConeAlgebra.lean` `true_cone_iff` / `ProfileSpectralCone.lean`, Ap… |
| `emit_sturm_positive.py` | `sturm_positive` | Sturm strict-interval-positivity emitter — `0 < p(x)` for all `x ∈ [a, b]`, with a Sturm sequence as the exact decision oracle. |
| `emit_symmetric_quad.py` | `symmetric_quad` | Symmetric moment-matrix PSD emitter — the SYMBOLIC-IN-n completing-the-square certificate (the marquee P=NP unblocker). |
| `emit_symmetric_quad_d2.py` | `symmetric_quad_d2` | Symmetric moment-matrix PSD emitter, DEGREE 2 — the symbolic-in-n three-piece completing-the-square + Cauchy–Schwarz decomposition of the level-2 subset form. |
| `emit_tangent.py` | `tangent` | Tangent-line-trick emitter — a symmetric-sum (combinatorial) inequality. |
| `emit_telescope.py` | `telescope` | Telescoping-potential emitter — the README-tracked-open "generic induction emission for telescoping potentials", as a first-class shape. |
| `emit_tight_cap_enclosure.py` | `tight_cap_enclosure` | BG g-step "tight-cap enclosure" emitter — the FIXED-named-config closure faces. |
| `emit_transcendental_enclosure.py` | `transcendental_enclosure` | Transcendental-enclosure emitter — rational lower/upper bounds for a transcendental expression over a box, kernel-checked via Mathlib. |
| `emit_turan_box.py` | — | Turan-box convenience emitter (#5): log-concavity a1^2 >= a0*a2 over a rational box. |
| `emit_turing_band.py` | `turing_band` | T5 Turing-band emitter: per-band Lean instantiation of TuringBand.turing_band_on_line. |
| `emit_two_row_solve.py` | `two_row_solve` | TwoRowSolveBound emitter — solution-entry bounds for a 2×2 scalar system, distilled from the OpenAI Navier--Stokes blowup formalization (`github.com/openai/NavierStokesAndEuler`, `NavierStokes/OutgoingPulseBounds.lean` `two_row_solution_… |
| `emit_two_scale_separation.py` | `two_scale_separation` | Two-scale separation emitter — an inner-disk point and an outer-sphere point are separated. |
| `emit_twofreq_offline.py` | `twofreq_offline` | twofreq_offline emitter -- certified OFF-line displacement of a two-frequency section. |
| `emit_twopoint_moment.py` | `twopoint_moment` | TwoPointMomentFeasibility emitter — explicit discrete-measure moment witnesses, distilled from the OpenAI Navier--Stokes blowup formalization (`github.com/openai/NavierStokesAndEuler`, `NavierStokes/LoopMoments.lean` `exists_projected_tw… |
| `emit_typed_cavity_induction.py` | `typed_cavity_induction` | typed_cavity_induction emitter -- a finite TYPE TABLE with per-type bounds is an inductive invariant of a branching (tree) recursion over every finite rooted tree. |
| `emit_unimodal.py` | `unimodal` | Unimodal integer-maximum emitter — the README-tracked-open "generic Lean lemma for unimodal integer maxima", as a first-class shape. |
| `emit_unit_modulus_sos.py` | `unit_modulus_sos` | Unit-modulus (conjugate-pair) SOS emitter — Hermitian positivity from \|u\| = 1. |
| `emit_weil_form_enclosure.py` | `weil_form_enclosure` | Weil-form enclosure emitter -- the E8 pairing as a NAMED-HYPOTHESIS trust seam. |
| `emit_winding_box_zero.py` | `winding_box_zero` | Winding-box-zero emitter — Arb-trust-class winding-number box certificate for a zero. |
| `emit_winding_count.py` | `winding_count` | Winding-count numeric core + KERNEL emitter (Stage 2A). |
| `emit_window_form_floor.py` | `window_form_floor` | Window-form-floor emitter -- Zhu's one-stroke window reduction as a certificate shape. |
| `emit_wz.py` | `wz` | WZ / Zeilberger creative-telescoping emitter — machine-checkable certificates for hypergeometric / binomial SUM IDENTITIES `Σ_k F(n,k) = rhs(n)`. |
| `emit_xi_line_zeros.py` | `xi_line_zeros` | xi_line_zeros emitter (Stage 1 core): on-line zero count via sign changes + IVT. |
| `emit_xor3.py` | `xor3_moment` | 3-XOR moment-matrix PSD emitter — GF(2) closure → block-rank-one SOS. |
| `emit_zero_free_cosine.py` | `zero_free_cosine` | Zero-free-region nonnegative-cosine-polynomial emitter. |
| `emit_zero_free_region.py` | — | Zero-free-region assembly emitter. |
| `emit_zero_sum_majorant.py` | `zero_sum_majorant` | zero_sum_majorant emitter -- a zero-supported family is summable through a finite ordinate window plus the local-count tail `m(rho) C/(1 + \|gamma_rho\|^2)`. |
<!-- EMITTERS:END -->

## License

Business Source License 1.1: free for research, teaching and peer review; see [LICENSE](LICENSE).
Contributions require the contributor license agreement in [CLA.md](CLA.md). The mathematics and Lean
code elsewhere in this repository are Apache-2.0; see [../LICENSING.md](../LICENSING.md).
