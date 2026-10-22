# The paper: class number one without L-functions

This folder holds the paper for the second kernel-checked proof of the class number one theorem, the one we call the
determinant route. It sits beside the first paper (in `paper/` at the top of the repository), which proves the same Lean
statement through OpenAI's 7/8 zero-free region and the Chowla–Selberg formula. We are keeping both on purpose. The point of
the second paper is partly the proof itself and partly the comparison: what changes when you take the L-function, the zeta
function and the zero-free theorem out of the closure, and what that costs.

- `paper.tex` is the source, and `paper.pdf` is the built paper (28 pages, including Appendix A and the references).
- The paper is archived as version 1.1.0 of the tenth-discriminant Zenodo record, DOI
  [10.5281/zenodo.23563656](https://doi.org/10.5281/zenodo.23563656) (reserved, not yet published). The first paper is
  version 1.0.1 of the same record, DOI [10.5281/zenodo.23550992](https://doi.org/10.5281/zenodo.23550992), and the DOI
  for all versions is [10.5281/zenodo.23550257](https://doi.org/10.5281/zenodo.23550257).
- Appendix A (`appendix_siegel.tex`, read in by `paper.tex`) has remarks on the Siegel-zero determinant arguments that
  the route descends from. None of it is formalized, it is not part of the kernel-checked theorem, and it was checked only by a separate
  AI review session, not by a referee.
- `refs.bib` is the bibliography. The entries carried over from the first paper are unchanged. Each new
  entry was checked at its source; the provenance is in the comments of `refs.bib`.

## What the paper says

The theorem is the same one-screen Lean statement as before, `CN1.classNumber_eq_one_iff`: for squarefree m ≥ 1, ℚ(√−m) has
class number one exactly when m is one of 1, 2, 3, 7, 11, 19, 43, 67, 163. What is new is the route. If K has class number
one and its discriminant q is at least 2^15, every prime below q/4 is inert, and every split prime is a value of the norm
form. Counting lattice points under an ellipse then shows the split primes are sparse, so there is an inert prime R between
q^4 and q^5. Green's derivative determinant, built on a grid of algebraic integers, is nonzero modulo R by van Dijk's
finite-field argument. Frobenius at every inert prime up to R makes it divisible by a large power of that prime, and its
complex size is too small for all that divisibility. Below 2^15, a residue sieve over 4,095 integers, checked by the kernel in
eight chunks of about half a second each, together with two lemmas about the prime 2, leaves only the nine fields.

The paper is careful about one word. It does not call this proof "elementary". What it claims is narrower and checkable: no
L-function, no zeta function and no zero-free theorem in the proof's closure. The closure still contains integration, the
Minkowski convex-body theorem and Mathlib's Gamma function, and the paper says so.

## Credit

The argument is not ours. It is written out in a short, unrefereed note that we cite only by repository, path and commit:
twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae. That note builds on Lior Silberman's inertness
observation, Kyle Pratt's suggestions (the norm count, the auxiliary inert prime, and the residue sieve), Ben Green's
derivative determinant and its divisibility lemma, and Roelof van Dijk's finite-field nonvanishing argument, all made in or
around the comments of Terence Tao's tenth-discriminant challenge. Green also noted that essentially the same nonvanishing
argument is given in a paper posted by Jacob Pescador, which the paper cites; that overlap is Green's observation, and we
have not compared the two arguments ourselves. The paper records Green's, van Dijk's and Pescador's own statements
about AI use word for word, and notes where the companion extends their lemmas (the full ring of integers, a single maximal
minor, and the prime 2).

## How it was checked

All eight steps are proved, each with the three standard axioms, and an independent AI review session (not a referee) has
checked the interface and all eight steps. The assembled theorem then went through one frozen run of record. Comparator
accepted it under both nanoda and Lean's own kernel, in about 148 seconds and 6.3 GB (a local run, not sandboxed, as are
all the Comparator runs described here). A walk over its closure of 69,295
constants found only the three standard axioms and no constant from any L-series, zeta, Euler-product or modular-form
module. Twelve recorded checks, nine of them controls that had to fail, all printed their expected lines. The paper's §7 has
the details, including where Mathlib's Gamma function enters (only through the Minkowski bound used for the nine fields) and
the fact that Stirling's formula and Wallis are not in the closure.

The review session then re-ran Comparator and the closure audit with its own build of the project and of nanoda, and ran five
controls of its own. Its build compiled all 55 project modules from source, and Comparator accepted the theorem again under
both kernels, in about 137 seconds and 6.3 GB.
Its own closure audit found 69,293 constants; the difference of two is exactly the auxiliary recursors `Lean.Syntax.rec_1` and
`Lean.Syntax.rec_2`, which one walk follows and the other does not. Its five controls all failed as they should,
including one that slips a false lemma past the elaborator with `debug.skipKernelTC`: `#print axioms` still shows only the
standard three for that one, and only the kernels' re-check rejects it. These runs share the Comparator and lean4export
binaries and the Lean toolchain with the run of record; nanoda is the independent kernel.

A note on the Lean files for Lemma 2: its θ(x) and B parts are proved but not used by the final theorem; only the A(m) part
is.

The published Lean files differ from the checked ones in comments only: built side by side, they give a byte-identical
export of the theorem's closure (`determinant/formalization/VERIFICATION.md` has the method). A fresh copy builds from the public
lakefile in about 3.4 minutes: about 150 seconds to download Mathlib's prebuilt files from its official cache, then 8,980
jobs in about 53 seconds. Mathlib itself is not recompiled, and its cached files were not replayed through a kernel in that fresh copy; the
Mathlib constants of the closure were re-checked by both kernels in the run of record, against the same Mathlib revision.

The author read back the final paper and the verification record on 22 October 2026, and approved them.

Continuous integration is green. The workflow "determinant proof" (`.github/workflows/determinant.yml`) runs on a
GitHub-hosted `ubuntu-latest` runner with Mathlib from its official cache. On 22 October 2026 it passed at commit
`80354fa2`, on both the push and the pull-request trigger. Each run first tests the check scripts against their fixtures (54
cases, including a crafted bypass attempt) and regenerates the eight sieve chunks byte for byte. It then builds
`lake build ELEM CN1 CN1Challenges` (8,984 jobs, the vendored first-proof modules included), finds exactly one `sorry` warning,
the challenge statement's, and checks that the axiom report of a file importing only `ELEM.Main` is, as a whole, a single list
of exactly `propext`, `Classical.choice` and `Quot.sound`. That is also the Linux build; the fresh-copy build above was on macOS.

## Checking the theorem yourself: one rule

Do not write a file that imports `ELEM.Main` together with `CN1Challenges.ClassNumberOne` or any module under
`ELEMNegControls/`. All of them declare `CN1.classNumber_eq_one_iff`, and Lean silently merges same-type declarations on
import: `#print axioms` then reports the cached axioms of one module for the proof term of another, so a proof that uses
`sorry` or a postulated axiom can look clean. Use Comparator (challenge `CN1Challenges.ClassNumberOne`, solution
`ELEM.Main`), or audit the axioms by walking the closure in an environment whose only project import is `ELEM.Main`. In the
verification run described in the paper's §7, two duplicate-declaration audit controls broke this rule on purpose, and both
failed as they should. Those controls are not in the public tree; it carries only the two tampered statements, under
`ELEMNegControls/Tamper/`.

## Building it

You need a TeX distribution with `pdflatex` and `bibtex`:

```sh
pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper
```

The build has no errors and no undefined references. Module paths in the paper are the actual public ones, under
`determinant/formalization/` in this repository (for example `determinant/formalization/ELEM/Count/Lattice.lean`).
