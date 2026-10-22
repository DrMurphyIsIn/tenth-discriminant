# VERIFICATION.md

This file records two things about the Lean files in this directory: that they compile to exactly the same declarations as the
files that went through the run of record, and that a fresh copy of this directory builds from the public lakefile.

## 1. The published files are the checked files

### What changed

The run of record (paper, §7) was made on a frozen tree whose comments and docstrings still carried internal references: section
numbers of our working plan, the names of the work tracks that proved each step, labels from the review, and private file paths.
Before publishing we removed those, from comments and docstrings only. Nothing else in a Lean module changed. In detail:

- **60 Lean modules** are published: 42 in `ELEM/`, 15 in `CN1/`, the challenge `CN1Challenges/ClassNumberOne.lean`, and the two
  tampered statements in `ELEMNegControls/Tamper/`.
- **32 of them are byte-identical** to the checked files. These include the challenge (md5 `c162eee687881e61b454bfe698507de7`),
  all 15 vendored `CN1` modules, which are in turn byte-identical to the files in `../../formalization/CN1/`, and both tampered
  statements.
- **28 differ in comments and docstrings only**: 20 `ELEM` modules, and the 8 generated sieve chunks, whose header comment now
  names `determinant/certificates/gen_sieve.py` instead of a private path. The docstring of `CN1.classNumber_eq_one_iff` in
  `ELEM/Main.lean`, which must match the challenge's, was not touched.
- **One checked file is not published:** the negative control that proves the theorem from a postulated false bound. As for
  the first proof, a file that declares a false axiom does not
  belong in a public library. Nothing else imports it.
- **The lakefile** differs as build configuration must: the checked tree pointed `packagesDir` at a local, already-built package
  directory, and the public one fetches Mathlib from git at the same revision; its comments were rewritten; and its control
  library no longer has the false-bound file to collect. `lake-manifest.json` differs only in `packagesDir`: every package is at
  the same revision as in the checked tree's manifest, and those revisions are the ones Mathlib `d13f23b` itself pins.
  `lean-toolchain` is unchanged (`leanprover/lean4:v4.34.1`).

### How we checked it

We used two methods: one on the source text, and a stronger one on the compiled declarations.

**On the text.** [`scripts/strip_comments_compare.py`](scripts/strip_comments_compare.py) removes comments and docstrings from every
module of two trees and compares what is left, with whitespace collapsed. Run against the checked tree, it reports all 60 published
modules `SAME`, and the false-bound control as present only in the checked tree.

**On the compiled declarations.** We built both trees from source, side by side, in scratch copies against the same Mathlib
package directory (the one the run of record used), and compared what Lean produced:

1. **The checked tree (A)**: a copy of the frozen sources with their original lakefile and manifest.
2. **The published tree (B)**: a copy of this directory, with one line added to its lakefile, and the `packagesDir` line of its
   manifest changed, so that both point `packagesDir` at the same package directory, so that both builds use the same compiled Mathlib.

Each tree was built with `lake build ELEM CN1` (exit 0; 8,982 jobs; all 57 modules of `ELEM` and `CN1` compiled from source in
each). Then, in each:

- **lean4export** (version 3.1.0, the same binary Comparator used in the run of record, md5 `b8b81a76f7622ddc89d0c55ebe1382cc`)
  exported `CN1.classNumber_eq_one_iff` and its entire dependency closure, starting from `ELEM.Main`:
  `lake env lean4export ELEM.Main -- CN1.classNumber_eq_one_iff`. This is the export that Comparator's kernels replay. It
  contains every declaration's name, universe parameters, type and value, but no docstrings. We made it twice: once in the default
  form, and once with `--export-mdata`, which also keeps the metadata annotations inside expressions.
- **[`scripts/ConstHashes.lean`](scripts/ConstHashes.lean)**, which imports every module of `ELEM` and `CN1`, listed every constant
  declared in those modules (1,049 of them, including the declarations that the main theorem does not use and the auxiliary
  declarations Lean generates) with its kind, universe parameters, and the structural hashes of its type and value.

The results:

| Output | Tree A (checked) | Tree B (published) | Comparison |
|---|---|---|---|
| lean4export, closure of `CN1.classNumber_eq_one_iff` | md5 `5b1cacd123ee8724c9719f839196f514`, 528,419,066 bytes | md5 `5b1cacd123ee8724c9719f839196f514`, 528,419,066 bytes | byte-identical |
| the same, with `--export-mdata` | md5 `225d8cb226f9bd3dc0f32082c166d670`, 529,896,381 bytes | md5 `225d8cb226f9bd3dc0f32082c166d670`, 529,896,381 bytes | byte-identical |
| ConstHashes, all 1,049 `ELEM` and `CN1` constants | md5 `9b91f26f5eb463ce3c50b27710fd2e5a`, 87,509 bytes | md5 `9b91f26f5eb463ce3c50b27710fd2e5a`, 87,509 bytes | byte-identical |

So the published modules compile to the same declarations, term for term, as the modules of the run of record, and the closure
that Comparator checked is the closure of the published theorem.

The export also gives an independent count of that closure. It contains 53,241 theorems, 12,722 definitions, 1,055 inductive
types (with 1,162 constructors and 1,057 recursors), 51 opaque constants, 4 quotient constants and exactly 3 axioms: `propext`,
`Quot.sound` and `Classical.choice`. That is 69,295 constants, the same count, kind by kind, as the closure audit of the run of
record (paper, §7.3).

**A control for the method.** A comparison that always says "identical" proves nothing, so we also changed one proof term in the
closure, without changing any statement, and repeated the check. In a third copy (C) of the published tree, the proof of
`ELEM.Primes.log_four_eq` (`log 4 = 2 * log 2`, used by Chebyshev's bound) was given one extra, unused line,
`have _h : (1 : ℕ) = 1 := rfl`, which leaves its statement alone and changes its proof term. After a rebuild (exit 0, 8,982
jobs), both comparisons with the checked tree failed, as they should:
- the lean4export of the closure differed (md5 `7d3d03770fff2f60749e9214fd03e219`, 528,419,262 bytes, against 528,419,066);
- the ConstHashes listing differed in exactly one line, the value hash of `ELEM.Primes.log_four_eq`, with its type hash
  unchanged.

## 2. A fresh build from the public lakefile

We copied this directory, with no build state, into a scratch location outside both trees and ran the published instructions:
`lake exe cache get`, then `lake build`. To exercise the network download, which the fresh build of the first proof did not, we
pointed `MATHLIB_CACHE_DIR` at a new, empty directory, so nothing could come from this machine's existing Mathlib cache, and the
copy had no `.lake/packages` directory, so every package was cloned from GitHub. The Lean toolchain v4.34.1 was already installed
through elan.

| Step | Exit code | Wall time | Jobs |
|---|---|---|---|
| `lake exe cache get`: clone Mathlib and its eight dependencies at their pins, build the cache tool, download and unpack 8,908 cache files from `cache.mathlib.org` | 0 | 149.9 s | (42 jobs for the cache tool) |
| `lake build` (the default target, `ELEM`) | 0 | 52.5 s | 8,980 jobs: "Build completed successfully (8980 jobs)." |
| `lake build CN1Challenges ELEMNegControls` (the statement and the two tampered statements) | 0 | 10.4 s | 8,928 jobs, almost all already up to date |

So a clean copy goes from nothing to a built proof in about 3.4 minutes (202 s) on this machine (Apple M3 Ultra, 32 cores,
96 GB, macOS 26.6), most of it the download; the project's own modules compile in under a minute. The fetch used about 8 GB of
disk.

After the build, in the same copy:
- every package in `.lake/packages` was at the revision `lake-manifest.json` pins, with no local changes: Mathlib `d13f23b7`,
  batteries `f2effa3d`, aesop `355695d5`, Qq `6a489d9a`, proofwidgets `106ff4fa`, plausible `118aa17e`, importGraph `e928b725`,
  LeanSearchClient `ddf04cf3` and Cli `e92c9f15`;
- `#print axioms CN1.classNumber_eq_one_iff`, in a file whose only import is `ELEM.Main`, printed
  `'CN1.classNumber_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound]`, and `scripts/check_axioms.sh` passed;
- the build of the workflow at that time, `lake build ELEM CN1Challenges`, then succeeded (exit 0, 8,982 jobs). Its log has
  exactly one `sorry` warning, at `CN1Challenges/ClassNumberOne.lean:32:8`, the statement, and `scripts/check_no_sorry.sh` passes
  on it. The log of plain `lake build` has no `sorry` warning at all, because it does not build the challenge, and the log of the
  build that includes the tampered statements has three; the current script rejects both, as it should (all three logs are
  fixtures in `scripts/fixtures/sorry/`). The workflow now builds `ELEM CN1 CN1Challenges`, so that every vendored module,
  `CN1.Foundations.Ramified` included, is compiled too.

What this did not test: Linux, and Comparator inside the fresh copy. The workflow in `../../.github/workflows/determinant.yml`
had not run when this build was made, because it can only run on GitHub. It has since passed on a GitHub-hosted Ubuntu runner,
first on 22 October 2026 at commit `413d3b142` (the first Linux build), and then, with the strict checks of section 3, at commit
`80354fa2` (runs `39827301611` and `39827310062`, on the push and the pull-request trigger: self-test 54 of 54, sieve
regeneration, `lake build ELEM CN1 CN1Challenges` with 8,984 jobs, the sorry check and the axiom check). The paper's §7.8
records the runs.

## 3. The sieve chunks and the axiom check

- `../certificates/regenerate_and_diff.sh` regenerates the eight sieve chunks from `gen_sieve.py` and finds them byte-identical to
  the files in `ELEM/Sieve/`. Before we edited the generator's comments and the header line it writes, the original generator
  reproduced the checked chunks byte for byte, and both negative controls as well.
- **The two check scripts, and a correction.** The first published version of
  [`scripts/check_axioms.sh`](scripts/check_axioms.sh) read the axiom list after the *last* `[` in Lean's output. The independent
  review showed, with real Lean v4.34.1 output, that this can be fooled: Lean prints an axiom named `«#evil[»` unescaped, as
  `[#evil[, propext, Classical.choice, Quot.sound]`, and the old script then saw only the three standard axioms. The theorem
  itself was never affected (its real output is the standard three, and Comparator checks the axioms independently), but the
  repository's only automated axiom gate was weaker than described. The script now requires the whole output, with whitespace
  removed, to be exactly one report for `CN1.classNumber_eq_one_iff` in which every entry is one of `propext`,
  `Classical.choice` and `Quot.sound`, with only an optional `info:` position prefix. [`scripts/check_no_sorry.sh`](scripts/check_no_sorry.sh) was tightened at the same
  time: it now requires a log that reports a successful build and contains exactly one `sorry`, the challenge statement's, and it
  fails closed on a missing, empty or failed-build log.
- **The self-test.** [`scripts/test_checks.sh`](scripts/test_checks.sh) runs both scripts over the 52 fixtures in
  [`scripts/fixtures/`](scripts/fixtures), sorted into `accept/` and `reject/`, and over a missing file. The fixtures whose names
  begin with `real_` are captured output: the CI run's and the fresh build's axiom reports and build logs, the run of record's
  axiom log, the `«#evil[»` attack and a three-line wrapped list printed by real Lean, and the build log that includes the tampered
  statements. The others are constructed: `sorryAx`, `Lean.ofReduceBool` and `native_decide` auxiliary axioms, on one line and on
  continuation lines; look-alike names; duplicated, second and foreign reports; unclosed and empty lists; error lines; an empty
  file; a wrong theorem name; and sorry warnings in every position and format. All 54 cases behave as expected. Run against the
  two earlier versions of the scripts, the same self-test reports 16 cases wrong, among them the `«#evil[»` attack. The workflow
  runs the self-test before it builds anything. Run locally in the fresh copy of section 2, the revised workflow's steps all
  passed: the self-test, the sieve regeneration, `lake build ELEM CN1 CN1Challenges` (exit 0, 8,984 jobs, now including
  `CN1.Foundations.Ramified`), the sorry check and the axiom check.
