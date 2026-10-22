# determinant/formalization/

This is the Lean 4 project of the determinant proof. It proves `CN1.classNumber_eq_one_iff`, the class number one theorem for
imaginary quadratic fields, with no L-function, no zeta function and no zero-free theorem in its closure. It is pinned to:
- Lean v4.34.1;
- Mathlib at revision d13f23b723b8a846827a245b89c10fc7d3f11612, required directly. That is the same Mathlib as the first proof in
  [`../../formalization/`](../../formalization/README.md), but this project does not depend on openai/math or on any patched
  package. Every other entry in [`lake-manifest.json`](lake-manifest.json) is one of Mathlib's own dependencies, at the revision
  Mathlib pins.

## The libraries

| Library | What it is |
|---|---|
| `CN1Challenges` | [`CN1Challenges/ClassNumberOne.lean`](CN1Challenges/ClassNumberOne.lean), the statement with `sorry`, copied unchanged from the first proof (md5 `c162eee687881e61b454bfe698507de7`). It imports only Mathlib. |
| `ELEM` | The new development, one module per step of the argument. [`ELEM/Main.lean`](ELEM/Main.lean) is the solution module: it states `CN1.classNumber_eq_one_iff` with the challenge's docstring and statement byte for byte, and proves it. |
| `CN1` | Fifteen modules vendored verbatim from the first proof: its Mathlib-only foundations (`CN1.Foundations.*`) and its finite part (`CN1.Finite.*`). They are byte-identical to the files in `../../formalization/CN1/`. None of them imports openai/math; their header comments mention it only as the environment in which they were first written. No analytic module of the first proof is present. |
| `ELEMNegControls` | The two tampered statements, [`Tamper/DropSquarefree.lean`](ELEMNegControls/Tamper/DropSquarefree.lean) and [`Tamper/Nine167.lean`](ELEMNegControls/Tamper/Nine167.lean), copied unchanged from the first proof. Comparator must reject both against `ELEM.Main`. They are never imported by `ELEM`. Their header comment still names the first proof's solution module `CN1.Main`; here the solution is `ELEM.Main`. |

## The modules, step by step

The development was built around a fixed interface. [`ELEM/Defs.lean`](ELEM/Defs.lean) defines the shared objects,
[`ELEM/Hypotheses.lean`](ELEM/Hypotheses.lean) states the eight steps of the argument as propositions, and
[`ELEM/Glue.lean`](ELEM/Glue.lean) proves the challenge statement from those eight propositions, taken as explicit hypotheses. Each
step is then proved separately against its fixed statement. Equation numbers are those of the companion note
(twinheterodox/tenth-discriminant, companions/elementary, commit 64694aae).

| Step of the argument | Module | Main declarations |
|---|---|---|
| The shared objects: ℤ[ω], inertness, the sums over primes, the derivative matrix and its minors | `ELEM.Defs` | `cq`, `OK`, `Fp2`, `IsInert`, `IsSplit`, `A`, `Iinert`, `Splus`, `M`, `minor`, `Delta` |
| The eight fixed statements, and the analytic setting | `ELEM.Hypotheses` | `AnalyticSetting`, `LemmaTwoA`, `SplitBound`, `AuxPrime`, `Nonvanishing`, `SizeBound`, `DivisibilityBound`, `Endpoint`, `Sieve` |
| From class number one to the analytic setting; the prime 2; the finite side; the assembly | `ELEM.Glue` | `analyticSetting_of_classNumber_eq_one`, `isWitness_two_of_not_mod_four`, `isWitness_two_of_mod_eight`, `classNumber_ne_one_of_lt`, `classNumber_eq_one_iff_of_hyps` |
| Frobenius at an inert prime is conjugation (p = 2 included) | `ELEM.Frobenius` | `pow_char_eq_star`, `frobenius_dvd` |
| Lemma 2: Chebyshev-type estimates for A(m), θ(x) and B | `ELEM.Primes.*` | `theta_lt_three_halves_mul`, `sum_log_div_sq_lt_two_thirds`, `lemmaTwoA` |
| (6), (7), (8): split primes are sparse (lattice count, Abel summation) | `ELEM.Count.Lattice`, `.Partial`, `.SplitBound` | `card_split_le`, `split_weight_le`, `splitBound` |
| Lemma 3: an inert prime R with q⁴ < R ≤ q⁵ | `ELEM.Count.AuxPrime` | `auxPrime` |
| §4.1: some maximal minor is nonzero mod R (van Dijk's root count) | `ELEM.Nonvanishing.Hermite`, `.Minor`, `.Params`, `.Main` | `derivMatrix_rows_linearIndependent`, `nonvanishing` |
| (11): the size of the minor, in Leibniz form | `ELEM.Size.Leibniz`, `.Embedding`, `.Bound` | `norm_det_le_factorial_mul_prod`, `sizeBound` |
| (12)-(14): divisibility at the inert primes (Green's row replacement) | `ELEM.Divisibility.Det`, `.Rows`, `.Count`, `.Main` | `pow_two_mul_dvd_norm_minor`, `divisibilityBound` |
| (15)-(17): the endpoint, pure real arithmetic | `ELEM.Endpoint.Monotone`, `.Comparison` | `log_le_of_large`, `final_comparison`, `endpoint` |
| §6: the residue sieve below 2^15 | `ELEM.Sieve.Defs`, `.Chunk0` … `.Chunk7`, `.Range`, `.Main` | `sieveOK_chunk0` … `sieveOK_chunk7`, `sieve` |
| The split-prime criterion and the converse for the nine fields (Minkowski), vendored | `CN1.Finite.SplitPrime`, `.Converse`, `.Bridge` | `classNumber_ne_one_of_isWitness`, `classNumber_eq_one_of_mem_nine`, `classNumber_eq_one_of_foundations` |
| The theorem | `ELEM.Main` | `CN1.classNumber_eq_one_iff` |

The eight chunk files `ELEM/Sieve/Chunk*.lean` are generated; their generator is in [`../certificates/`](../certificates/README.md).
Each is a single `decide +kernel` over 512 values of k. A few declarations are proved but not used by the main theorem (for
example `LemmaTwoTheta` and `LemmaTwoB`, whose finite-set forms the divisibility step uses instead); their docstrings say so where
it could be confusing.

## Building

You need [elan](https://github.com/leanprover/elan) and git. From this directory:

```sh
lake exe cache get                    # download Mathlib's build cache
lake build ELEM CN1Challenges         # the proof and the statement; plain `lake build` builds ELEM
```

No patches are needed, and nothing outside Mathlib and its own dependencies is fetched. **Do not run `lake update`**: it would move
the pins. [`VERIFICATION.md`](VERIFICATION.md) records a build of a fresh copy of this directory, with its wall time and job
count.

## Checking the axioms, and the one rule

```sh
printf 'import ELEM.Main\n\n#print axioms CN1.classNumber_eq_one_iff\n' > AxiomCheck.lean
lake env lean AxiomCheck.lean > axioms.out 2>&1
scripts/check_axioms.sh axioms.out
```

This should print `OK: CN1.classNumber_eq_one_iff depends only on: propext Classical.choice Quot.sound`.
[`scripts/check_axioms.sh`](scripts/check_axioms.sh) joins the output into one line before reading it, because Lean prints a long
axiom list one entry per line, and a line-based check would miss an entry on a continuation line.
[`scripts/check_no_sorry.sh`](scripts/check_no_sorry.sh) checks a build log for `sorry` outside `CN1Challenges`. The GitHub Actions
workflow in [`../../.github/workflows/determinant.yml`](../../.github/workflows/determinant.yml) runs both after a clean build.

**The one rule.** Do not write a file that imports `ELEM.Main` together with `CN1Challenges.ClassNumberOne` or any module under
`ELEMNegControls/`. All of them declare `CN1.classNumber_eq_one_iff`, and Lean silently merges same-type declarations on import:
`#print axioms` then reports the cached axioms of one module for the proof term of another, so a proof that uses `sorry` or a
postulated axiom can look clean. Use Comparator (challenge `CN1Challenges.ClassNumberOne`, solution `ELEM.Main`), or check the
axioms in a file whose only project import is `ELEM.Main`, as above.

`#print axioms` reads a summary stored with the compiled modules, so even used correctly it is a convenient check, not the
strongest one. The run of record also walked the closure of the theorem directly, without that summary, and the paper (§7.3)
reports the result.

## Checking with Comparator

[Comparator](https://github.com/leanprover/comparator) checks that a solution proves a separately written statement, using only
permitted axioms, and replays the proof through Lean's kernel and, optionally, through [nanoda](https://github.com/ammkrn/nanoda_lib),
an independent reimplementation of the kernel. The configurations of the run of record are in [`comparator/`](comparator):

| Configuration | Challenge | Expected verdict |
|---|---|---|
| [`ClassNumberOne.json`](comparator/ClassNumberOne.json) | the statement of record | "Your solution is okay!" (nanoda and Lean's kernel both accept) |
| [`Tamper_DropSquarefree.json`](comparator/Tamper_DropSquarefree.json) | the statement without `Squarefree m` (false: m = 4) | rejected: "Challenge and solution theorem statement do not match" |
| [`Tamper_Nine167.json`](comparator/Tamper_Nine167.json) | 163 replaced by 167 (false: ℚ(√−167) has class number 11) | rejected: statement mismatch |

Each permits only `propext`, `Quot.sound` and `Classical.choice`, with nanoda switched on. To run them:
1. Build Comparator at tag v4.34.0 with toolchain v4.34.1, together with its `lean4export`, and build nanoda.
2. Set `COMPARATOR_LEAN4EXPORT` and `COMPARATOR_NANODA` to those binaries, and `COMPARATOR_LANDRUN` to landrun.
3. Build the modules (`lake build ELEM CN1Challenges ELEMNegControls`), then from this directory run
   `lake env comparator comparator/<config>.json`.

landrun is Linux-only. Our runs were on macOS, with a pass-through shim in its place, so they were **not sandboxed**. In the run of
record the real configuration was accepted by both kernels in about 148 seconds with a peak of about 6.3 GB, and both tampered
configurations were rejected with the expected line. A third control, a proof routed through a postulated false bound, was rejected
too ("Illegal axiom detected"); as for the first proof, that file is not published.

## The published files and the checked files

The run of record was made on a tree whose comments still carried internal references (plan section numbers, names of work
tracks, private paths). We removed those from the comments and docstrings, and changed nothing else.
[`VERIFICATION.md`](VERIFICATION.md) records how we checked that, and [`scripts/strip_comments_compare.py`](scripts/strip_comments_compare.py)
is the text-level half of that check.
