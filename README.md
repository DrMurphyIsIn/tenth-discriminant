# The tenth discriminant

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23550258.svg)](https://doi.org/10.5281/zenodo.23550258)

This repository is our entry for Terence Tao's
[experimental AI-math challenge](https://terrytao.wordpress.com/2026/10/20/an-experimental-ai-math-challenge-using-tenth-discriminant-bounds-to-explore-arguments-ruling-out-siegel-zeroes/)
of 20 October 2026. The challenge is to take one of the new arguments around Siegel zeroes and the quasi-Riemann hypothesis, and
use it to bound a hypothetical tenth imaginary quadratic field of class number one, without Heegner's method.

We went one step further than a bound. This repository contains a complete, **kernel-checked** Lean 4 proof of the class number
one theorem itself:

> For squarefree m ≥ 1, the field ℚ(√−m) has class number one if and only if m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}.

The proof uses no Heegner, Baker, Stark or Gross–Zagier input. It goes through OpenAI's theorem that no Dirichlet L-function
vanishes when Re s > 7/8, the Chowla–Selberg formula evaluated at s = 7/8, and a split-prime criterion for the finitely many
fields that remain. Along the way it proves, in Lean, the explicit bound that any tenth discriminant would have to satisfy:
**d ≤ 652**.

There are three ways in, depending on what you want:

- **The paper**, [`paper/paper.pdf`](paper/paper.pdf): the mathematics and the verification record, about twenty pages.
- **The readable proof**, [`notes/proof.md`](notes/proof.md): the same argument step by step, with the Lean lemma for each step and
  a link to its file and line. It takes about an hour.
- **The Lean**, [`formalization/`](formalization/README.md): build it and run the checks yourself.

## The statement, and what you have to trust

The theorem is stated in [`formalization/CN1Challenges/ClassNumberOne.lean`](formalization/CN1Challenges/ClassNumberOne.lean),
using only Mathlib's definitions:

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

You do **not** need to trust OpenAI's 7/8 theorem, our code, or any AI. OpenAI's manuscript is unrefereed, but its Lean proof sits
inside the dependency closure that the kernels checked.

## The argument in six steps

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

## How it was checked

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
- **Independent replay.** A separate AI review session is replaying the final checks with its own build and its own copy of
  nanoda, on the same machine and with the same Comparator and lean4export binaries. Its result was not in yet when v1.0.0 was archived; it will be
  recorded here, and in a later archived version.
- **Caveats.** Our Comparator runs are local and do not use Comparator's sandbox. The logs, the source manifest and the tool
  hashes are available on request. The scripts that generated the numerical tables
  and the witness primes are not trusted: the kernel re-checks every fact they emit.

## Building and checking it yourself

You need [elan](https://github.com/leanprover/elan), git and Python 3. From [`formalization/`](formalization/README.md):

```sh
scripts/apply_oai_patches.sh   # fetch the pinned dependencies and apply openai/math's Lean-v4.34.1 patches
lake exe cache get             # Mathlib build cache
lake build CN1.Main CN1Challenges
```

Do not run `lake update`; the formalization README explains why. [`formalization/README.md`](formalization/README.md)
also explains how to run Comparator on the real statement and on the tampered ones. [`certificates/regenerate_and_diff.sh`](certificates/README.md)
regenerates the generated Lean files and checks them byte for byte.

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

## The method, and Telperion

This work follows the discipline of [Telperion](telperion/README.md), the certificate engine we have been developing. Everything a
language model produces (numbers, enclosures, witnesses and proof drafts) is untrusted input, and only the Lean kernel may accept
it. A hallucinated bound does not become a theorem: it fails to check. Here the discipline was applied by hand rather than through
the engine. The generators in [`certificates/`](certificates/README.md) are standalone scripts, and the kernel re-checks
everything they emit. What remains is the risk that the *statement* says the wrong thing. That is why the statement was written
first and independently reviewed before the assembly that proves it was built, and why the tampered statements are part of the
check.

Our own audits, including known-answer tests, have caught real soundness bugs in our tools. We fixed them and disclosed them
([#739](https://github.com/DrMurphyIsIn/Arda/pull/739), [#740](https://github.com/DrMurphyIsIn/Arda/pull/740) in our public Arda
repository). We think this is one practical answer to a question Tao and others have been raising: how to get the benefit of AI
assistance in mathematics without trusting what the AI says.

*Note on the vendored copy:* `telperion/` is the same v0.1.6 snapshot that ships with our Brualdi–Goldwasser repository, and it
**predates those fixes**: its `arb_dh` winding-number routine samples the boundary rather than certifying it, and the
`emit_baez_duarte` emitter is still present. Nothing in this project runs the vendored engine; it is included as the reference implementation of the method described above.
A newer snapshot, under review, will replace it.

## Credits

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

## Citing

Please cite the archived release, [doi:10.5281/zenodo.23550258](https://doi.org/10.5281/zenodo.23550258); see
[`CITATION.cff`](CITATION.cff).

## AI use

This work was done with extensive use of AI assistance (Anthropic's Claude), in separate sessions. One session did the work.
Another, independent session reviewed the statement before the assembly that proves it was built, read every module in full before
the run of record, and is replaying the final checks with its own build. The mathematical route is due to the people credited
above. The mathematical claims are kernel-checked; the history, the attributions and the account of how the work was checked are
ours, and we say how each was obtained.

## Licensing

The mathematics (Lean, generators, frozen certificates, scripts) is Apache-2.0, and the documents (including the paper) are
CC-BY-4.0. `telperion/` is under the Business Source License 1.1, which permits research, teaching, review and evaluation
outright. See [LICENSING.md](LICENSING.md).
