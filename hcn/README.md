# Class number two

This directory is the third entry in this repository. It is a **kernel-checked** Lean 4 proof that the imaginary quadratic
fields of class number at most two are exactly the 27 known ones:

> For squarefree m ≥ 1, the field ℚ(√−m) has class number at most two if and only if m is one of
> 1, 2, 3, 7, 11, 19, 43, 67, 163 (class number one) or
> 5, 6, 10, 13, 15, 22, 35, 37, 51, 58, 91, 115, 123, 187, 235, 267, 403, 427 (class number two);
> and it has class number exactly two if and only if m is one of those eighteen.

The theorem is classical: Baker and Stark solved the class number two problem in 1971. What is new here is a proof by the
route of the first entry, extended from one class to every class, and checked by two kernels. Like the first proof, it does
not use Heegner's method (no j-invariant or singular moduli occur in the closure), linear forms in logarithms, or the
Gross–Zagier formula. It does use modular objects: the Jacobi theta function and its modular transformation, and, through
OpenAI's proof of the 7/8 theorem, non-holomorphic Eisenstein series with their automorphy. Its deep input is OpenAI's theorem that no Dirichlet
L-function vanishes when Re s > 7/8, and the Lean proof of that theorem is inside the checked closure, not assumed.

There are two ways in:

- **The paper**, [`paper/paper.pdf`](paper/paper.pdf): the mathematics, the verification record, and a comparison with the
  repository's two proofs of class number one.
- **The Lean**, [`formalization/`](formalization/README.md): build it and run the checks yourself.

The generators for the statement's two sets and for the 1,447 certificates of the finite range, with the computed class-number
data they read, are in [`certificates/`](certificates/README.md).

## How it builds on the first proof

The first proof showed that a tenth field of class number one would have to have d = |disc K| ≤ 652. It wrote the Dedekind
zeta function of K as half the Epstein zeta function of the principal form, which only works when every ideal is principal,
continued it to s = 7/8 with the Chowla–Selberg formula, and used the 7/8 theorem to make L(7/8, χ) ≥ 0 while ζ(7/8) < 0.

With two classes, ζ_K is no longer one Epstein zeta function, but it is a sum of them, one per ideal class. That is the
extension LemmaLab posted in the comments of Tao's challenge: sum the Chowla–Selberg expansion over the classes, using only that
the principal form occurs and that every leading coefficient is bounded. LemmaLab certified, in ball arithmetic, that every field
with class number at most two has d ≤ 4164. This entry formalizes that extension, in the form that Mathlib and the first proof
make provable:

1. **ζ_K splits into class sums.** For K = ℚ(√−m), m ∉ {1, 3}, ζ_K(s) = Σ_C ½ Z_{Q_C}(s) on Re s > 1, a sum over Mathlib's class
   group. Mathlib has no binary quadratic forms and no reduction theory, so each class C is represented by an ideal J in C⁻¹
   with its Hermite basis, and Q_C is the norm form of that basis. Its leading coefficient a_C satisfies 1 ≤ a_C ≤ N(J), and
   Minkowski's bound, in Mathlib's form, gives N(J) ≤ (2/3)√d. The principal class has a_C = 1.
2. **Chowla–Selberg for every positive definite form.** Each ½ Z_{Q_C} continues to s = 7/8 as a_C^(−7/8) ζ(7/4), plus a
   negative multiple of ζ(3/4) of size about d^(−3/8), plus a remainder bounded by an explicit function of a_C that increases
   with a_C. The remainder bound keeps the first proof's kernel bound, with its halved exponent, and splits the double sum more
   sharply; the formula specializes to the first proof's at a = 1.
3. **The threshold.** At s = 7/8 the left side is ζ(7/8) L(7/8, χ) ≤ 0, by the 7/8 theorem. If the class number is at most
   two and d ≥ 4778, the right side is positive. So class number at most two forces **d ≤ 4777**. To close at 4778 with the
   first proof's enclosures, the positive y = 0 term of the non-principal class has to be kept: without it the margin is about
   2·10⁻⁵, which the proved enclosure of Γ(3/8)/Γ(7/8) cannot resolve; with it the margin is about 0.069.
4. **The finite range.** Below 4778 there are 1,456 fields. For the 1,429 outside the known 27, a short certificate, which
   uses only which numbers the principal norm form represents, shows class number at least three. For the eighteen, explicit
   ideal witnesses show class number exactly two. For the nine, the first proof's theorem `CN1.classNumber_eq_one_iff` gives
   class number one.

The first proof's Lean files are vendored here verbatim (41 modules under `formalization/CN1/`), and this proof uses its
foundations, its factorization ζ_K = ζ · L, its kernel integral, its enclosures of ζ and Γ, its positivity L(7/8, χ) ≥ 0, and,
for the nine fields, its main theorem. The repository's second proof of class number one, the determinant route, is not used:
a zero-free half-plane bounds the class number of every field, while the determinant argument, as formalized, starts from
class number one directly.

## The statement, and what you have to trust

The two statements are [`formalization/HCNChallenges/ClassNumberLeTwo.lean`](formalization/HCNChallenges/ClassNumberLeTwo.lean),
in the vocabulary of the first entry:

```lean
theorem HCN.classNumber_le_two_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K ≤ 2 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163, 5, 6, 10, 13, 15, 22, 35, 37, 51, 58, 91, 115, 123, 187, 235, 267, 403, 427} : Finset ℕ)

theorem HCN.classNumber_eq_two_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 2 ↔ m ∈ ({5, 6, 10, 13, 15, 22, 35, 37, 51, 58, 91, 115, 123, 187, 235, 267, 403, 427} : Finset ℕ)
```

The two sets were generated from computed class-number data, never typed by hand, and a reader can check them against the
classical lists. To believe the result you need to trust the same four things as for the first proof:
- that these statements say what they should, together with the Mathlib definitions they use;
- the Lean kernel;
- the independent nanoda kernel;
- the three standard axioms (`propext`, `Quot.sound`, `Classical.choice`).

You do not need to trust OpenAI's 7/8 theorem, our code, the class-number data or any AI. The 7/8 theorem's manuscript is
unrefereed, but its Lean proof is walked, as a theorem, inside the closure that the kernels checked.

## Credits

As the paper gives them:

- **The challenge** is Terence Tao's.
- **The quasi-Riemann hypothesis at 7/8** for all Dirichlet L-functions, with its Lean proof, is OpenAI's
  ([openai/math](https://github.com/openai/math), family 003, Apache-2.0).
- **The Chowla–Selberg formula** is S. Chowla's and A. Selberg's. In the comments of Tao's post, michaelmross gave the
  expansion of the principal form by Poisson summation, Tao observed that together with the 7/8 theorem it gives d < 655, and
  LemmaLab evaluated it at the fixed point s = 7/8 and certified d ≤ 653 in ball arithmetic.
- **The extension to all class numbers** is LemmaLab's: through the Epstein zeta functions of all h classes, with d ≤ 4164
  certified for h ≤ 2 (comment 698478). The analytic half of this proof is that extension, in the form that Mathlib and the
  first proof make provable.
- **The classical solution** of the class number two problem is due to A. Baker and H. M. Stark (1971).
- **Tools:** Mathlib and its contributors, for the number-field, class-group, ideal-norm, L-series, Gamma, Mellin and
  Poisson-summation infrastructure; the authors of the packages OpenAI's proof builds on, including PrimeNumberTheoremAnd and
  RellichKondrachov; Chris Bailey for nanoda, the second kernel; and the authors of Comparator and lean4export.

The paper also discusses related work: Watkins's determination of all class numbers up to 100, and, from October 2026,
Kimura's unconditional determination up to 2000, whose analytic bounds are proved in Lean. We do not claim priority among Lean
formalizations of results of this kind. We claim a kernel-checked proof by this route.

## Building it and checking it

Everything is in [`formalization/`](formalization/README.md). It uses the same pinned openai/math as the first entry, with the
same patch script:

```sh
scripts/apply_oai_patches.sh              # fetch the pinned dependencies and apply openai/math's Lean-v4.34.1 patches (once)
lake exe cache get                        # Mathlib's build cache
lake build HCN CN1 HCNChallenges          # the proof, the vendored first proof, and the statements
```

openai/math and its analysis packages are compiled from source; [`formalization/VERIFICATION.md`](formalization/VERIFICATION.md)
records how long that takes from a fresh copy.

### One rule

**Do not write a file that imports `HCN.Main` together with `HCNChallenges.ClassNumberLeTwo` or any module under
`HCNNegControls/`.** All of them declare `HCN.classNumber_le_two_iff` and `HCN.classNumber_eq_two_iff`, and Lean silently merges
same-type declarations on import: `#print axioms` then reports the cached axioms of one module for the proof term of another, so
a proof that uses `sorry` or a postulated axiom could look clean. The run of record tested this on purpose: an audit that
imported `HCN.Main` together with the challenge walked the challenge's `sorry` term for both theorems, while `collectAxioms`
still reported the standard three; the audit caught it, and failed as it should. That control is a recorded run, not a module,
so there is nothing to import. Use Comparator (challenge `HCNChallenges.ClassNumberLeTwo`, solution `HCN.Main`), or check the
axioms in a file whose only project import is `HCN.Main`, as the repository's GitHub Actions workflow does.

## How it was checked

The details are in the paper's verification section. In brief:

- **Comparator, with two kernels.** Comparator (tag v4.34.0) checked that `HCN.Main` proves exactly the two challenge
  statements, with only the three permitted axioms, and replayed the proof through nanoda and through Lean's own kernel. Both
  accepted it: "Your solution is okay!", in about 660 seconds. The runs were local and not sandboxed.
- **The closure audit.** A walk over the closure of both theorems, in an environment that imports `HCN.Main` and nothing else of
  the project, found 135,435 constants and exactly the three standard axioms, with no `sorryAx` and no `unsafe` constant.
  OpenAI's `LFunction_ne_zero_of_seven_eighths_lt_re` is in the closure as a theorem, so its proof is walked, not assumed. Two
  packages that OpenAI's proof uses, PrimeNumberTheoremAnd and RellichKondrachov, enter the closure with OpenAI's published
  patches; the patched files add no `sorry`, axiom, `native_decide`, `unsafe` or `extern`.
- **Controls.** Twelve recorded checks, ten of them controls that must fail, all printed their expected lines. Comparator rejected
  the three tampered statements in [`formalization/HCNNegControls/Tamper/`](formalization/HCNNegControls/Tamper): 163 moved
  into the class-number-two set, `Squarefree m` dropped, and 427 replaced by 431 (whose class number is 21). It also rejected
  three tampered proofs, through a postulated false bound, a postulated threshold, and one certificate step replaced by `sorry`,
  and the closure audit rejected the same three. As in the other entries, those three files are not published: a file that
  declares a false axiom, or replaces a step of a proof by `sorry`, does not belong in a public library (the challenge and the
  tampered statements are statements left as `sorry` by design, as Comparator requires).
- **Independent replay.** A separate AI review session rebuilt the project, re-ran Comparator with its own build of nanoda, and
  ran five controls of its own; both kernels accepted the theorems again. It is an AI review, not a referee's report.
- **The published files are the checked files.** Before publishing we removed internal references from the Lean comments and
  docstrings, corrected the worst-case figures at d = 4778 in the docstring of `HCN.Numerics.Threshold`, added one sentence
  to the docstring of `Bg_mono`, and rewrote three stale remarks; nothing else in the Lean sources changed. The build configuration is replaced by a public one, with openai/math from git at the pinned
  commit. [`formalization/VERIFICATION.md`](formalization/VERIFICATION.md) records how we checked that the published modules
  compile to exactly the same declarations as the checked ones, the build of a fresh copy, and a fresh Comparator run on the
  published challenge and tampered statements.

## What is and is not claimed

**Claimed:** a kernel-checked Lean proof, by the route above, that the imaginary quadratic fields of class number at most two
are exactly the 27, and those of class number two exactly the 18, checked by Comparator under two kernels with only the three
standard axioms.

**Not claimed:**
- the theorem, which is classical (Baker and Stark, 1971), or the route, which is the thread's;
- priority among Lean formalizations of results of this kind;
- anything about the Riemann hypothesis, or about Siegel zeros beyond what the 7/8 theorem itself gives;
- optimality: the threshold 4777 is far from what the method can reach, and the finite half certifies h ≥ 3 field by field
  without computing class numbers;
- any theory of binary quadratic forms: the development has no reduction, no composition, no genus theory, and no
  correspondence between forms and ideal classes, and it proves nothing about class numbers above two.

The 7/8 theorem's manuscript is, as far as we know, unrefereed. Its Lean proof is inside the checked closure, so its correctness
is not in question in the sense that matters for the kernel; a refereed human understanding of why it is true does not yet
exist. The paper describes the mathematics and the checking without itself being checked by anything: where it says what a
Lean lemma states, the lemma is the authority.

## Layout

- [`formalization/`](formalization/README.md): the Lean project (libraries `HCN`, `CN1`, `HCNChallenges`, `HCNNegControls`), with
  [`VERIFICATION.md`](formalization/VERIFICATION.md) and the check scripts.
- [`certificates/`](certificates/README.md): the generators, the class-number data, and `regenerate_and_diff.sh`.
- [`paper/`](paper/): the paper.

## AI use

As for the other entries, this work was done with extensive use of AI assistance (Anthropic's Claude), in separate sessions.
Several sessions did the work, one for each part of the plan. Another, independent session reviewed the plan, the statements and
the delivered parts, and replayed the run of record with its own build of the project and of nanoda, with five controls of its
own. The class-number data behind the two statements were computed by scripts and by PARI, and cross-checked by independent
code; the proof does not rely on them. The mathematical route is due to the people credited above. The mathematical claims are
kernel-checked; the history, the attributions and the account of how the work was checked are ours, and we say how each was
obtained.
