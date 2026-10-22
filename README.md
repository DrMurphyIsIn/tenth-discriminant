# The tenth discriminant

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23550257.svg)](https://doi.org/10.5281/zenodo.23550257)

This repository is our entry for Terence Tao's
[experimental AI-math challenge](https://terrytao.wordpress.com/2026/10/20/an-experimental-ai-math-challenge-using-tenth-discriminant-bounds-to-explore-arguments-ruling-out-siegel-zeroes/)
of 20 October 2026. The challenge is to take one of the new arguments around Siegel zeroes and the quasi-Riemann hypothesis, and
use it to bound a hypothetical tenth imaginary quadratic field of class number one, without Heegner's method.

We went one step further than a bound. This repository contains not one but two complete, **kernel-checked** Lean 4 proofs of the
class number one theorem itself:

> For squarefree m ≥ 1, the field ℚ(√−m) has class number one if and only if m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}.

Neither proof uses Heegner, Baker, Stark or Gross–Zagier input. Both prove the same Lean statement, word for word, with the same
trust base. They get there by very different routes, though they are not independent of each other: they share the statement, the
foundational modules and the converse (the Minkowski-bound proof that the nine fields do have class number one).

- **The first proof** goes through OpenAI's theorem that no Dirichlet L-function vanishes when Re s > 7/8, the Chowla–Selberg
  formula evaluated at s = 7/8, and a split-prime criterion for the finitely many fields that remain. Along the way it proves, in
  Lean, the explicit bound that any tenth discriminant would have to satisfy: **d ≤ 652**. It lives in
  [`formalization/`](formalization/README.md), [`paper/`](paper/README.md) and [`notes/`](notes/README.md).
- **The second proof, the determinant route**, has **no L-function, no zeta function and no zero-free theorem in its closure**, and
  needs nothing beyond Mathlib and its dependencies. It runs the engine of the recent Siegel-zero arguments, Green's derivative determinant made
  nonzero by van Dijk's finite-field argument, directly on class number one, and shows that a tenth discriminant would be below
  2^15; a residue sieve, checked by the kernel, does the rest. It lives in [`determinant/`](determinant/README.md).

We have kept the first proof exactly as it was. It is the comparison point: the second paper's §8 sets the two side by side and
says what it costs to take the L-function out of the closure.

There are several ways in, depending on what you want:

- **The papers**: [`paper/paper.pdf`](paper/paper.pdf) for the first proof, about twenty pages, and
  [`determinant/paper/paper.pdf`](determinant/paper/paper.pdf) for the determinant route and the comparison, 28 pages.
- **The readable proof** of the first route, [`notes/proof.md`](notes/proof.md): the argument step by step, with the Lean lemma for
  each step and a link to its file and line. It takes about an hour.
- **The Lean**: [`formalization/`](formalization/README.md) and [`determinant/formalization/`](determinant/formalization/README.md).
  Build them and run the checks yourself.

## The statement, and what you have to trust

The theorem is stated in [`formalization/CN1Challenges/ClassNumberOne.lean`](formalization/CN1Challenges/ClassNumberOne.lean),
using only Mathlib's definitions. The determinant route uses an unchanged copy of the same file, so both proofs answer exactly this
statement:

```lean
theorem CN1.classNumber_eq_one_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)
```

A quadratic field that contains a square root of −m, with m squarefree, is ℚ(√−m), so this says exactly what the classical
theorem says. The squarefree hypothesis matters: without it, m = 4 with K = ℚ(i) would be a counterexample.

To believe the result you need to trust four things:
- that this statement says what it should, together with the Mathlib definitions it uses;
- the Lean kernel;
- the independent nanoda kernel;
- the three standard axioms (`propext`, `Quot.sound`, `Classical.choice`).

You do **not** need to trust OpenAI's 7/8 theorem, our code, or any AI. For the first proof, OpenAI's manuscript is unrefereed, but
its Lean proof sits inside the dependency closure that the kernels checked. For the determinant route, OpenAI's proof is not in the
closure at all, and neither is anything else beyond Mathlib and its dependencies.

## The first proof: the argument in six steps

The route was worked out in the comments of Tao's post (see Credits). Write K = ℚ(√−m), and d = |disc K|, so that d = m when
m ≡ 3 (mod 4) and d = 4m otherwise. Let χ be the character of K. Suppose K has class number one and m ≠ 1, 3.

1. **ζ_K is an Epstein zeta function.** Every ideal is principal and the only units are ±1, so ζ_K(s) = ½ Σ′ Q(x, y)^(−s). Here Q
   is the principal form: x² + xy + ((d + 1)/4)y², or x² + (d/4)y².
2. **ζ_K = ζ · L(·, χ).**
3. **Chowla–Selberg.** Poisson summation in one variable continues ½ Σ′ Q^(−s) past Re s = 1. It equals
   ζ(2s) + 2^(2s−1)√π Γ(s − ½)/Γ(s) · d^(½−s) ζ(2s − 1), plus a K-Bessel series of size about e^(−π√d). The Lean proof bounds
   that series explicitly.
4. **The bound at s = 7/8.** There the main part is M(d) = ζ(7/4) + C d^(−3/8) ζ(3/4), with C = 2^(3/4)√π Γ(3/8)/Γ(7/8) ≈ 6.4847.
   Because ζ(3/4) < 0, M increases with d. It vanishes at d* = 653.98763…. The Lean proof shows that M(d) minus the remainder bound
   is positive for every d ≥ 655.
5. **The contradiction.** ζ(7/8) < 0, so for d ≥ 655 the value L(7/8, χ) = ζ_K(7/8)/ζ(7/8) is negative. But L(σ, χ) > 0 for
   σ > 1, and by OpenAI's theorem L has no zero on (7/8, 1], so by continuity L(7/8, χ) ≥ 0. Hence d < 655. A discriminant is
   ≡ 0 or 3 (mod 4), so **d ≤ 652**.
6. **The finite range.** Suppose a prime p < (d + 1)/4 splits in K. A prime ideal above p would then be principal, so p = Q(x, y),
   which a short argument rules out for such a small p. So K does not have class number one. For each of the 190 squarefree
   non-Heegner m with d ≤ 652, the Lean proof exhibits such a prime, checked by the kernel; the largest needed is p = 31. The prime
   must split, not merely be small: for d = 8 the prime 2 lies below the bound but is ramified, and ℚ(√−2) does have class number
   one.

The converse, that the nine fields do have class number one, is also proved in Lean, from the Minkowski bound.

## How the first proof was checked

All of this is in more detail in the paper, §4.

- **Axioms.** `#print axioms CN1.classNumber_eq_one_iff` reports `[propext, Classical.choice, Quot.sound]`. There is no `sorry`,
  `native_decide` or `axiom` in the proof. The only `sorry`s in the project are in the challenge statements, as Comparator requires, and in the three candidate phrasings
  of the statement kept in `CN1Challenges/Candidates.lean` (type-checked only).
- **Comparator, with two kernels.** [Comparator](https://github.com/leanprover/comparator) (tag v4.34.0) checks that the proof
  proves exactly the statement above and uses only the permitted axioms. It then replays the proof through two independent kernels,
  [nanoda](https://github.com/ammkrn/nanoda_lib) and Lean's own. The run of record was made from a frozen source tree, every file of
  which was hashed before and after the run. Both kernels accepted the proof: "Your solution is okay!".
- **The published files are the checked files.** Before publishing, we removed internal references from the Lean *comments*. A
  comment-stripping script then confirmed that, with comments removed, every published Lean module (all 45) is identical to the
  checked one. Comparator was then run again on exactly the Lean modules and Comparator configurations in this repository, built
  against the same patched dependency tree as the run of record, and again both kernels accepted the proof.
- **Tampered statements are rejected.** Comparator rejects the statement with `Squarefree m` deleted, and the statement with 163
  replaced by 167, as not matching the proof. Both are in
  [`formalization/CN1Challenges/Tamper/`](formalization/CN1Challenges/Tamper), with their configurations, so you can rerun them.
  Two tampered *proofs* were rejected too, as "Illegal axiom detected": one postulates a false bound as an axiom, the other closes it
  with `sorry`. They are not published, because a file that declares a false axiom does not belong in a public library.
  Both tampered statements were rejected again when Comparator was rerun on the files in this repository.
- **Dependency audit.** The proof's dependency closure has 129,170 constants:
  - Mathlib;
  - Lean core, and Mathlib's own dependencies Batteries and Aesop;
  - 26,740 from openai/math, all in its Dirichlet L-function development (family 003);
  - 1,028 of ours;
  - two analysis packages that OpenAI's proof imports, PrimeNumberTheoremAnd and RellichKondrachov. Both are at the commits
    openai/math pins, with OpenAI's published patches, and we verified that the patches match exactly.

  A scan of every name in the closure found no declaration or module named after Heegner, Baker, Stark, Goldfeld or Gross–Zagier,
  apart from our own (the main theorem, the converse lemmas and the list `nonHeegner190`), and no classification of
  class-number-one fields. The PrimeNumberTheoremAnd commit pinned by openai/math has two `sorry`s in `Wiener.lean`. OpenAI's patch
  removes them, and `sorryAx` is not in the closure.
- **Independent replay.** A separate AI review session replayed the final checks and accepted the proof under both kernels. It
  used its own build of this project's modules and its own build of nanoda, against the same verified dependency tree, with the
  same Comparator and lean4export binaries, on the same machine; it was local and not sandboxed. It also rejected two further
  tampers: the statement with 163 removed from the list, and a proof routed through `native_decide`. Its independent audit of the
  dependency closure agrees with ours.
- **A clean copy builds.** Following the instructions below, a clean copy of this repository's `formalization/` directory, with
  no build state, fetched and patched its dependencies from GitHub and completed all 11,914 build jobs (about an hour on Apple silicon). The main theorem reports only the three standard axioms. One
  step was not exercised: `lake exe cache get` took Mathlib's build cache from this machine's local cache, not from the network.
  The test did not cover Linux, or running Comparator inside that copy.
- **Caveats.** Our Comparator runs are local and do not use Comparator's sandbox. The logs, the source manifest and the tool
  hashes are available on request. The scripts that generated the numerical tables
  and the witness primes are not trusted: the kernel re-checks every fact they emit.

## The second proof: the determinant route

The full story is in [`determinant/README.md`](determinant/README.md) and the second paper. Here is the shape. Write q = |disc K|
(the d above). Suppose K has class number one.

1. **Small primes are inert.** If q ≥ 2^15, every prime p < q/4 is inert, by the same split-prime criterion as the first proof's
   step 6. That forces q to be a prime ≡ 3 (mod 8), and every split prime to be a value of the norm form.
2. **Split primes are sparse.** Counting lattice points under an ellipse bounds the split primes up to t by about πt/(2√q).
3. **An auxiliary inert prime.** Chebyshev-type estimates then give an inert prime R with q⁴ < R ≤ q⁵.
4. **The determinant is not zero.** Green's derivative determinant, on a grid of algebraic integers, has a maximal minor D₀ that is
   nonzero modulo R, by van Dijk's root count over the finite field, where Frobenius is conjugation.
5. **It is divisible by a lot.** At every inert prime p ≤ R, Frobenius again makes z^p − z̄ divisible by p, and Green's row
   replacement shows that the norm of D₀ is divisible by a large power of p.
6. **It is too small for that.** The size of the entries bounds log N(D₀) from above, and the inert primes push it up faster. With
   explicit constants, the two bounds are incompatible once q ≥ 2^15.
7. **Below 2^15.** A residue sieve of the 4,095 integers q ≡ 3 (mod 8) by the primes 3, …, 31, checked by the kernel in eight
   chunks, leaves only 11, 19, 43, 67 and 163; two short lemmas about the prime 2 handle every other residue class.

The converse, that the nine fields do have class number one, is the first proof's, from the Minkowski bound. The determinant
bound, q < 2^15, is much weaker than d ≤ 652, and the finite range is fifty times larger, yet the sieve that settles it is smaller
and cheaper than the first proof's list of witnesses. We do not call this proof elementary: its closure still contains integration,
the Minkowski convex-body theorem and Mathlib's Gamma function. What it does not contain is any L-function, any zeta function or
any zero-free theorem.

It was checked the same way as the first proof, on one frozen tree: Comparator accepted it under nanoda and Lean's kernel (in
local runs, not sandboxed), a walk over its closure of 69,295 constants found only the three standard axioms, nothing from
Mathlib's L-series, zeta or modular-form modules and nothing beyond Mathlib and its dependencies (Lean core, Batteries, Aesop)
apart from the project's own code, and twelve recorded checks, controls included, behaved as expected. A separate AI review session
then re-ran Comparator and the closure audit with its own build of the project's modules and of nanoda, and ran five controls of
its own: both kernels accepted the theorem again, its closure audit agreed, and all five controls failed as required. The
published files compile to exactly the same declarations as the checked ones, and a fresh copy builds from the public lakefile in
about 3.4 minutes; the second paper's §7.6 records both. The author read back the final paper and the verification record on
22 October 2026 and approved them, and the GitHub Actions workflow passed on a clean Linux runner the same day (§7.7 and §7.8).

## Building and checking it yourself

You need [elan](https://github.com/leanprover/elan), git and Python 3. For the first proof, from [`formalization/`](formalization/README.md):

```sh
scripts/apply_oai_patches.sh   # fetch the pinned dependencies and apply openai/math's Lean-v4.34.1 patches
lake exe cache get             # Mathlib build cache
lake build CN1.Main CN1Challenges
```

Do not run `lake update`; the formalization README explains why. [`formalization/README.md`](formalization/README.md)
also explains how to run Comparator on the real statement and on the tampered ones. [`certificates/regenerate_and_diff.sh`](certificates/README.md)
regenerates the generated Lean files and checks them byte for byte.

For the determinant route, from [`determinant/formalization/`](determinant/formalization/README.md), no patches are needed:

```sh
lake exe cache get             # Mathlib build cache
lake build ELEM CN1 CN1Challenges
```

Its README explains the axiom check and Comparator, and one rule that matters: never import `ELEM.Main` together with the
challenge or a control, because they declare the same theorem name. [`determinant/certificates/regenerate_and_diff.sh`](determinant/certificates/README.md)
regenerates the sieve chunks and checks them byte for byte. A GitHub Actions workflow,
[`.github/workflows/determinant.yml`](.github/workflows/determinant.yml), builds the determinant route from a clean checkout and
checks the axioms of its main theorem. All our Comparator runs, for both proofs, were local and not sandboxed: landrun, Comparator's
sandbox, is Linux-only, and on macOS we used a pass-through shim in its place. The first proof has no such workflow, because its build needs openai/math's patched
dependency tree and takes about an hour even on a fast machine.

## Repository layout

- [`paper/`](paper/README.md): the paper.
- [`notes/`](notes/README.md): the proof written out for a human reader, with the Lean name, file and line for each step.
- [`formalization/`](formalization/README.md): the Lean project. It has one module per step of the argument, the challenge
  statement, the tampered statements, and the Comparator configurations.
- [`certificates/`](certificates/README.md): the generators for the witness primes and the numerical tables in the Lean proof, with
  a script that regenerates them and checks them byte for byte.
- [`computations/`](computations/README.md): independent checks of step 4, in mpmath and in Arb ball arithmetic. These are not part
  of the proof.
- [`telperion/`](telperion/README.md): a vendored copy of the Telperion certificate engine.
- [`determinant/`](determinant/README.md): the second proof, the determinant route.
  - [`determinant/formalization/`](determinant/formalization/README.md): its Lean project, which requires only Mathlib, with
    the challenge statement, the tampered statements, the Comparator configurations, the check scripts and
    [`VERIFICATION.md`](determinant/formalization/VERIFICATION.md).
  - [`determinant/certificates/`](determinant/certificates/README.md): the generator for the residue sieve, with a script that
    regenerates the chunk files and checks them byte for byte.
  - [`determinant/paper/`](determinant/paper/README.md): the second paper, 28 pages.
- [`.github/workflows/`](.github/workflows/): continuous integration for the determinant route.

## The method, and Telperion

This work follows the discipline of [Telperion](telperion/README.md), the certificate engine we have been developing. Everything a
language model produces (numbers, enclosures, witnesses and proof drafts) is untrusted input, and only the Lean kernel may accept
it. A hallucinated bound does not become a theorem: it fails to check. Here the discipline was applied by hand rather than through
the engine. The generators in [`certificates/`](certificates/README.md) are standalone scripts, and the kernel re-checks
everything they emit. What remains is the risk that the *statement* says the wrong thing. That is why the statement was written
first and independently reviewed before the assembly that proves it was built, and why the tampered statements are part of the
check. The determinant route followed the same discipline, with one addition: its eight steps were stated as fixed propositions,
and reviewed, before the hard ones were proved, so that no step could weaken a neighbour's statement to make itself go through.

Our own audits, including known-answer tests, have caught real soundness bugs in our tools. We fixed them and disclosed them
([#739](https://github.com/DrMurphyIsIn/Arda/pull/739), [#740](https://github.com/DrMurphyIsIn/Arda/pull/740) in our public Arda
repository). We think this is one practical answer to a question Tao and others have been raising: how to get the benefit of AI
assistance in mathematics without trusting what the AI says.

*Note on the vendored copy:* `telperion/` is a snapshot of the engine at development commit `5b8eea03` (2026-10-18), which
includes those fixes. It is a selection, not a mirror: the complete engine source, plus selected tests, documents and examples.
Within those files it differs from the development version only in reworded comments, docstrings, Markdown wording and a few
string literals that pointed at private paths (see `telperion/README.md`, "About this copy"). Nothing in this project runs the vendored engine;
it is included as the reference implementation of the method described above.

## Credits

For the first proof:

- **The challenge:** T. Tao.
- **The 7/8 quasi-Riemann hypothesis** for all Dirichlet L-functions, with its Lean proof: OpenAI,
  [openai/math](https://github.com/openai/math), family 003.
- **The non-existence of Siegel zeroes, and its digests:** OpenAI; W. D. Banks (arXiv:2610.15483); B. Kerr (arXiv:2610.21099);
  B. Green.
- **The Chowla–Selberg formula:** S. Chowla and A. Selberg. In the thread, michaelmross gave the expansion of the principal form
  by Poisson summation. Tao observed that, with the 7/8 theorem, it gives d < 655. LemmaLab evaluated it at the fixed point
  s = 7/8 and certified d ≤ 653 in ball arithmetic. Our step 4 is that evaluation, now proved in Lean.
- **The finite step** is classical, in the spirit of Rabinowitsch's criterion. In the thread it was used by Lior Silberman (every
  small prime is inert under class number one), Kyle Pratt, twinheterodox and michaelmross.
- **Tools:** Mathlib, and the authors of the packages OpenAI's proof builds on, including PrimeNumberTheoremAnd and
  RellichKondrachov; nanoda; Comparator and lean4export.

For the determinant route (as the second paper's acknowledgments give them; [`determinant/README.md`](determinant/README.md) has
more):

- **The challenge:** T. Tao.
- **The argument:** the companion note twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae, which supplies the
  explicit constants and the assembly. The note states that it was prepared with OpenAI's Codex.
- **The inertness obstruction** under class number one: Lior Silberman, in the thread.
- **Counting norm representations** to bound the split primes, an auxiliary inert prime in a determinant argument, and the residue
  sieve: Kyle Pratt.
- **The derivative determinant** and its divisibility at inert primes: Ben Green.
- **The finite-field proof of nonvanishing:** Roelof van Dijk. Green noted that essentially the same argument is given in a paper
  posted by Jacob Pescador; that overlap is Green's observation, and we have not compared the two arguments ourselves.
- **Their statements about AI use:** Green credits ChatGPT 6 Astra for the arguments of his paper and claims no human originality;
  van Dijk attributes his new arguments to GPT-6 Astra and Opus 5.5; and Pescador states that all mathematics and text of the
  paper he posted were generated by AI systems (its byline names GPT-6 Pro and Claude Opus 5.5).
- **Tools:** Mathlib and its contributors; Chris Bailey for nanoda; the authors of Comparator and lean4export.

## Citing

Please cite the archived release: [doi:10.5281/zenodo.23550257](https://doi.org/10.5281/zenodo.23550257) for all versions,
which resolves to the latest. Version 1.1.0, [doi:10.5281/zenodo.23563656](https://doi.org/10.5281/zenodo.23563656), is the
first to contain both proofs and both papers. See [`CITATION.cff`](CITATION.cff).

## Versions

- **v1.1.0** ([doi:10.5281/zenodo.23563656](https://doi.org/10.5281/zenodo.23563656)):
  - adds the second proof, the determinant route, in [`determinant/`](determinant/README.md): its Lean project, the generator for
    its residue sieve, and its paper;
  - adds a GitHub Actions workflow that builds the determinant route and checks the axioms of its main theorem.

  The first proof, its certificates and its paper are unchanged.
- **v1.0.1** (2026-10-22, [doi:10.5281/zenodo.23550992](https://doi.org/10.5281/zenodo.23550992)):
  - records the independent replay and the fresh-clone build;
  - updates the vendored Telperion snapshot to development commit `5b8eea03`;
  - makes two wording corrections in the paper.

  The Lean proof and the certificates are unchanged.
- **v1.0.0** (2026-10-22, [doi:10.5281/zenodo.23550258](https://doi.org/10.5281/zenodo.23550258)): the first release.

## AI use

This work was done with extensive use of AI assistance (Anthropic's Claude), in separate sessions. One session did the work.
Another, independent session reviewed the statement before the assembly that proves it was built, read every module in full before
the run of record, and then replayed the final checks with its own build of our modules. For the determinant route, several sessions
did the work, one per step of the argument, and an independent session reviewed the plan, the interface and each delivered step,
and then re-ran Comparator and the closure audit with its own build of the project and of nanoda, and ran five controls of its
own. The mathematical routes are due to the people credited
above. The mathematical claims are kernel-checked; the history, the attributions and the account of how the work was checked are
ours, and we say how each was obtained.

## Licensing

The mathematics (Lean, generators, frozen certificates, scripts, in both proofs) is Apache-2.0, and the documents (including both
papers) are CC-BY-4.0. `telperion/` is under the Business Source License 1.1, which permits research, teaching, review and evaluation
outright. See [LICENSING.md](LICENSING.md).
