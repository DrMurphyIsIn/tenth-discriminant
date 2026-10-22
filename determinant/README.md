# The determinant route

This directory is the second entry in this repository. It is a new, **kernel-checked** Lean 4 proof of the same theorem that the
first entry proves:

> For squarefree m ≥ 1, the field ℚ(√−m) has class number one if and only if m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}.

The Lean statement is the same one, byte for byte, and so is the trust base. What changes is the route. The first proof goes
through OpenAI's theorem that no Dirichlet L-function vanishes when Re s > 7/8, and through the Chowla–Selberg formula at
s = 7/8. This one has **no L-function, no zeta function and no zero-free theorem in its closure**: not as a hypothesis, not as an
import that the proof leans on, and not hidden inside a dependency. It needs only Mathlib.

We have kept the first entry exactly as it was. The two proofs are worth having side by side, partly because they reach the same
statement from very different directions, and partly because the comparison shows what it costs to take the analytic number
theory of L-functions out of the closure. The paper's §8 makes that comparison in detail.

There are three ways in:

- **The paper**, [`paper/paper.pdf`](paper/paper.pdf): the mathematics, the verification record and the comparison with the first
  proof, 28 pages including an appendix and the references.
- **The Lean**, [`formalization/`](formalization/README.md): build it and run the checks yourself.
- **The sieve certificate**, [`certificates/`](certificates/README.md): the generator for the finite range, and a script that shows
  the checked-in Lean files are exactly what it produces.

## The idea, in one paragraph

Suppose K = ℚ(√−m) has class number one, and write q = |disc K|. If q ≥ 2^15, every prime p < q/4 is inert in K: a prime ideal of
norm p would have to be principal, and no non-rational element of the ring of integers has norm that small. That already forces q
to be a prime ≡ 3 (mod 8). Every split prime is the norm of an element, so the split primes up to t are bounded by a count of
lattice points in an ellipse, which is about πt/(2√q). Split primes are therefore sparse, and a weighted count of all primes
produces an inert prime R with q⁴ < R ≤ q⁵. Now take Ben Green's derivative determinant: a matrix whose rows are monomials z^r w^s
and whose columns are derivatives at the points (z, z̄) of a grid of algebraic integers, and D₀ one of its maximal minors. Modulo
R, Frobenius turns z̄ into z^R, and Roelof van Dijk's root count over the finite field shows that some D₀ is not zero. At every
inert prime p ≤ R, Frobenius again makes z^p − z̄ divisible by p, and a triangular change of rows shows that the norm of D₀ is
divisible by a large power of p. Add that up over the inert primes and you get a lower bound for log N(D₀) that outgrows the upper
bound coming from the size of the entries. The two bounds are incompatible once q ≥ 2^15. Below 2^15 the small primes finish the
job on their own: a sieve of the 4,095 integers q ≡ 3 (mod 8) by the primes 3, …, 31 leaves only 11, 19, 43, 67 and 163, and two
short lemmas about the prime 2 dispose of the other residue classes.

## Why there is no L-function in it

The recent arguments against Siegel zeros, by OpenAI, Green, van Dijk and others, have two parts: an engine and a conclusion. The
conclusion is a zero-free region, and the first proof uses exactly that, as a black box. The engine is the determinant. In
Green's and van Dijk's papers, a Siegel zero would force the inert primes to carry almost all of the weight Σ (log p)/p up to some
height, and the determinant is the device that shows they cannot: its divisibility at inert primes grows with that weight, and
its complex size does not.

Lior Silberman's observation, made in the comments of Tao's post, is that class number one forces the same extreme pattern
directly. Every prime below q/4 is inert, and by Kyle Pratt's count the split primes above are sparse. So the engine can be run
on class number one itself, with no L-function in between. That is the argument formalized here. It does not prove anything about
Siegel zeros, and we have formalized neither Green's theorem nor van Dijk's.

We are careful about one word. We do **not** call this proof elementary. Its closure contains Mathlib's measure theory and
interval integrals (the lattice count uses ∫₀¹ √(1 − x²) dx = π/4, and the partial summation is Abel summation). Through the
converse direction, which shows that the nine fields really do have class number one, it also contains the Minkowski convex-body
theorem and with it Mathlib's Gamma function. None of that is the analytic number theory of L-functions, but none of it is
elementary either. The claim is narrower and checkable: no L-function, no zeta function and no zero-free theorem in the closure.

## The statement, and what you have to trust

The statement is [`formalization/CN1Challenges/ClassNumberOne.lean`](formalization/CN1Challenges/ClassNumberOne.lean), an
unchanged copy of the first entry's file (md5 `c162eee687881e61b454bfe698507de7`):

```lean
theorem CN1.classNumber_eq_one_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)
```

The first entry's README explains why this phrasing pins down K = ℚ(√−m), and why the squarefree hypothesis matters. Because the
statement is identical, a reader who has accepted it for the first proof has nothing new to check on that side.

To believe the result you need to trust the same four things as before:
- that this statement says what it should, together with the Mathlib definitions it uses;
- the Lean kernel;
- the independent nanoda kernel;
- the three standard axioms (`propext`, `Quot.sound`, `Classical.choice`).

The list is shorter in one respect. The first proof did not ask you to trust OpenAI's 7/8 theorem, but it did put OpenAI's Lean
proof of it, and two further analysis packages, inside the closure that the kernels checked. Here none of that is present: the
project requires Mathlib directly, at the same revision `d13f23b` as the first entry, and nothing else.

## Credits

The mathematics is not ours, and we claim no part of it. These credits follow the acknowledgments of the paper.

- **The challenge** is Terence Tao's.
- **The argument** formalized here is that of the companion note twinheterodox/tenth-discriminant, companions/elementary, commit
  64694aae, which supplies the explicit constants and the assembly. The note states that it was prepared with OpenAI's Codex, and
  it is not refereed.
- **The inertness obstruction** under class number one was pointed out in the thread by **Lior Silberman**.
- **Kyle Pratt** suggested counting norm representations to bound the split primes, using an auxiliary inert prime in a
  determinant argument, and the residue sieve.
- **The derivative determinant** and its divisibility at inert primes are **Ben Green's**
  ([hexagon:2610.00311](https://hexagonmath.org/2610.00311v2), Lemma 5.1).
- **The finite-field proof of nonvanishing** is **Roelof van Dijk's** ([hexagon:2610.00409](https://hexagonmath.org/2610.00409)).
  Green noted that essentially the same argument is given in a paper posted by **Jacob Pescador**
  ([Landau–Siegel zeros and a Stepanov-type nonvanishing lemma](https://jacobpescador.github.io/ai-math/papers/landau-siegel-stepanov/));
  that overlap is Green's observation, and we have not compared the two arguments ourselves.
- **Their own statements about AI use**, recorded as they give them: Green credits ChatGPT 6 Astra for the arguments of his paper
  and claims no human originality; van Dijk attributes his new arguments to GPT-6 Astra and Opus 5.5; and Pescador states that all
  mathematics and text of the paper he posted were generated by AI systems (its byline names GPT-6 Pro and Claude Opus 5.5).
- **Tools:** Mathlib and its contributors, for the number-field, finite-field, polynomial, matrix and integration libraries the
  development uses throughout; Chris Bailey for nanoda; and the authors of Comparator and lean4export.

Green's Lemma 5.1 and van Dijk's nonvanishing argument are both stated for *odd* inert primes, in the order ℤ[√d], and Green
bounds the p-adic valuation of a Gram determinant. The full ring of integers ℤ[ω], the use of a single maximal minor in place of
the Gram determinant, and the prime p = 2 are the companion note's own extensions. Our own changes of route are small and are
listed in the paper's §1.3: the row-wise Leibniz bound in place of Hadamard's inequality, monotonicity in q through log t ≤ t − 1
with no derivatives, and a nonvanishing proof carried out directly over the finite field.

## Building it and checking it

Everything is in [`formalization/`](formalization/README.md). In short, from that directory:

```sh
lake exe cache get                    # download Mathlib's build cache
lake build ELEM CN1Challenges         # the proof and the statement
```

No patches and no other packages are needed. The README there lists the modules step by step, and explains how to run Comparator
and the axiom check.

### One rule

**Do not write a file that imports `ELEM.Main` together with `CN1Challenges.ClassNumberOne` or any module under
`ELEMNegControls/`.** All of them declare `CN1.classNumber_eq_one_iff`, and Lean silently merges same-type declarations on import:
`#print axioms` then reports the cached axioms of one module for the proof term of another, so a proof that uses `sorry` could
look clean. Use Comparator (challenge `CN1Challenges.ClassNumberOne`, solution `ELEM.Main`), or check the axioms in a file whose
only project import is `ELEM.Main`, as the repository's GitHub Actions workflow does. The independent review of this project found
this hazard, and the run of record tested it on purpose with two controls that break the rule and must fail.

## How it was checked

The details are in the paper, §7. In brief, one frozen source tree went through one run of record, in which the md5 of every
source file, of the build configuration and of every tool was recorded before and after; the tree did not change.

- **Comparator, with two kernels.** Comparator (tag v4.34.0) checked that `ELEM.Main` proves exactly the challenge statement, with
  only the three permitted axioms, and replayed the proof through nanoda and through Lean's own kernel. Both accepted it: "Your
  solution is okay!", in about 148 seconds and 6.3 GB.
- **The closure audit.** A walk over the closure of `CN1.classNumber_eq_one_iff`, in an environment that imports `ELEM.Main` and
  nothing else of the project, found 69,295 constants and only the three standard axioms, with no `sorryAx` and no `unsafe`
  constant. None of the constants comes from a module under any of the fourteen denied prefixes: Mathlib's `LSeries`,
  `EulerProduct`, `Harmonic.ZetaAsymp`, `ZetaValues`, `NumberField.DedekindZeta`, `ModularForms` and
  `ArithmeticFunction.LFunction`; openai/math, PrimeNumberTheoremAnd and RellichKondrachov; and the four analytic module families of
  the first proof. Every constant outside Mathlib, Lean core, Batteries and Aesop is from this project, and a scan of every name in
  the closure finds nothing named after Heegner, Baker, Stark, Gross, Zagier, Goldfeld, Heilbronn, L-functions, the Riemann zeta
  function, zero-free regions, 7/8 or Siegel.
- **Imports are not the claim.** The environment does *import* 69 modules from that list, `Mathlib.NumberTheory.LSeries.RiemannZeta`
  among them, because the files vendored from the first proof begin with `import Mathlib`. All 69 contribute nothing to the closure.
  The claim is about the constants the proof depends on, not about the import graph.
- **Where the Gamma function enters.** Only through the volume computations of the Minkowski convex-body theorem, in the converse
  for the nine fields. No constant of the analytic steps reaches it. Stirling's formula and the Wallis product are not in the
  closure.
- **Controls.** Twelve recorded checks, nine of them controls that must fail, all printed their expected lines. Comparator rejected
  the statement with `Squarefree m` deleted and the statement with 163 replaced by 167; both are in
  [`formalization/ELEMNegControls/Tamper/`](formalization/ELEMNegControls/Tamper), copied from the first entry. The kernel rejected
  the sieve chunk with 31 removed from the prime list and the chunk with 163 replaced by 167; [`certificates/`](certificates/README.md)
  regenerates both. A proof routed through a postulated false bound was rejected by Comparator ("Illegal axiom detected") and by
  the audit. As for the first entry, that file is not published, because a file that declares a false axiom does not belong in a
  public library.
- **The published files are the checked files.** Before publishing we removed internal references from the Lean comments and
  docstrings, and only there. [`formalization/VERIFICATION.md`](formalization/VERIFICATION.md) records how we checked that the
  published modules compile to exactly the same declarations as the checked ones, and the build of a fresh copy of this
  directory.
- **Independent replay.** A separate AI review session, not one of the sessions that wrote the proof, replayed the run of record
  (paper, §7.5). It copied the frozen tree, checked every file against the source manifest of the run of record, and compiled all
  the project modules that `ELEM.Main` and the challenge need from source, the eight sieve chunks included, with no compiled file
  from the run of record. Its second kernel was its own build of nanoda. Comparator accepted the solution again under both kernels,
  in about 137 seconds and 6.3 GB. Its own closure audit, importing `ELEM.Main` alone, passed with the same verdicts; it found
  69,293 constants, and the difference from 69,295 is exactly two auxiliary recursors of Lean's `Syntax` type that its walk does
  not follow. Five further controls of its own all failed as required, among them a solution that adds the false lemma 4 = 5 by
  switching off the elaborator's kernel check: `#print axioms` reports only the three standard axioms for that one, and both
  kernels rejected it. The replay used the same Comparator and lean4export binaries and the same Lean toolchain as the run of
  record, and the same shared, already-built Mathlib, so its independent kernel is nanoda; it was local and not sandboxed. It is
  an AI review, not a referee's report.

The paper's §7.6 summarizes the check that the published files are the checked ones, and the fresh build, both recorded in full
in [`formalization/VERIFICATION.md`](formalization/VERIFICATION.md). What is still open is listed in its §7.7: the author's own
check of the record, and continuous integration on GitHub.

## What is and is not claimed

**Claimed:** a kernel-checked Lean proof of the class number one theorem for imaginary quadratic fields whose closure contains no
L-function, no zeta function and no zero-free theorem, checked by Comparator under two kernels with only the three standard axioms.

**Not claimed:**
- that the proof is elementary (see above);
- the mathematics, which is the companion note's and the credited contributors';
- the theorem, which is classical (Heegner 1952, Baker 1966, Stark 1967);
- anything about Siegel zeros or the Riemann hypothesis: the proof uses no L-function at all;
- optimality: the cutoff 2^15 is far from what the method can reach, and the Leibniz bound and the endpoint are cruder than the
  source's. Those choices made the Lean shorter, not the mathematics sharper.

The companion note is unrefereed, and its own statement that it passed independent verification names no reviewer. We describe it
as formalized by us, not as verified by anyone else. Our Comparator runs were local and not sandboxed. The independent review is by
a separate AI session, not a human referee. And the paper describes the mathematics and the checking without itself being checked
by anything: where it says what a Lean lemma states, the lemma is the authority.

## Layout

- [`formalization/`](formalization/README.md): the Lean project (libraries `ELEM`, `CN1`, `CN1Challenges`, `ELEMNegControls`), with
  [`VERIFICATION.md`](formalization/VERIFICATION.md), [`SURFACE.md`](formalization/SURFACE.md) (the declarations the main
  theorem does not use) and the check scripts.
- [`certificates/`](certificates/README.md): `gen_sieve.py` and `regenerate_and_diff.sh`.
- [`paper/`](paper/README.md): `paper.tex`, `appendix_siegel.tex`, `refs.bib` and the built `paper.pdf` (28 pages), with a README
  that summarizes the paper and its state.

## AI use

As for the first entry, this work was done with extensive use of AI assistance (Anthropic's Claude), in separate sessions. Several
sessions did the work, one per step of the argument. Another, independent session reviewed the plan, the interface and the
delivered steps, and then replayed the final checks with its own build of the project and of nanoda. The mathematical route is due to the people credited above. The mathematical claims are kernel-checked; the
history, the attributions and the account of how the work was checked are ours, and we say how each was obtained.
