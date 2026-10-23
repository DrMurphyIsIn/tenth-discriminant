# VERIFICATION.md

This file records four things about the files in this directory and in `../certificates/`: that the Lean files compile to
exactly the same declarations as the files that went through the run of record, that the generators and the class-number data
reproduce what is checked in, that a fresh copy of this directory builds from the public lakefile, and that Comparator accepts
the published theorems against the published challenge and rejects the three published tampered statements.

## 1. The published files are the checked files

### What changed

The run of record (paper, verification section) was made on a tree whose comments and docstrings still carried internal
references: section numbers of our working plan, the names of the work tracks and of review items, and private file paths.
Before publishing we removed those. **Comments and docstrings of the Lean source files change, and nothing else in them**; the
build configuration is replaced by a public one. In detail:

- **79 Lean modules** are published: 34 in `HCN/`, 41 in `CN1/`, the challenge `HCNChallenges/ClassNumberLeTwo.lean`, and the
  three tampered statements in `HCNNegControls/Tamper/`.
- **The 38 modules of HCN, HCNChallenges and HCNNegControls all differ from the checked ones, in comments and docstrings only.**
  Twenty-four of them are generated (the statement, the 15 certificate chunks, `Certs`, `ClassTwo`, `Range`, `Assembly`, `Main`
  and the three tampered statements); for those the change was made in the generators' templates, and the generators were
  re-run (section 2). The other fourteen were edited by hand.
- **Comment changes that are not removals of internal references.** Almost every comment change removes an internal
  reference. These do more, and we list them all:
  - *One docstring correction.* The module docstring of `HCN.Numerics.Threshold` credited the worst case `-6.7e-5` at
    `D = 4778` to the Gamma enclosure alone. These are three different cases, and the docstring now gives all three: the
    proved enclosure 2.1753 ≤ Γ(3/8)/Γ(7/8) ≤ 2.1755 alone, with every other constant exact, gives about `-6.437e-5`; with
    the first proof's zeta enclosures as well (ζ(7/4) ≥ 1.96232, ζ(3/4) ≥ −3.44129) about `-6.697e-5`; and with the full
    chain of rational brackets about `-1.30e-3`. The mathematics of the module, and the margin `0.0687` it proves, are
    unchanged.
  - *One added sentence.* The docstring of `HCN.Statements.GeneralCS.Bg_mono` gained a sentence saying what is formalised:
    the weaker side condition `c ≥ 1/8` at the larger point, `HCN.CSAux.one_eighth_le_cst`.
  - *Three stale remarks rewritten.* The docstrings of `HCN.Assembly.LowerBound`, `HCN.Numerics.Threshold` and a section
    heading of `HCN.Statements.GeneralCS` still spoke of `sorry`ed statement files, from before those files were proved.
    They now say only which definitions and theorems are used.
  - *The challenge's module docstring* points to the first proof's challenge by its place in the repository, and has one
    added line saying that the tampered statements are made from it (below).
- **In the challenge, only the module docstring changed.** The checked challenge's md5 is `e0166de7111fd6b59764111e1b248f94`;
  the published one's is `00b03da302cae50b565b0c80380f4afc`. The two differ in the module docstring (lines 1 to 18) only. The
  docstring kept its length in lines, so lines 19 to 41 (the two theorem docstrings, the two statements and their `sorry`s)
  are byte-identical to the checked challenge's, at the same line numbers. This matters more than it might seem: Lean
  v4.34.1 labels each `sorry` with its source position, inside the proof term, so a challenge whose `sorry`s move export a
  different term. A first version of the scrub (md5 `1ab2d193ad095872fa23a3ab767c005e`), one line shorter, did exactly that:
  its statement export differed from the checked one by 29 bytes. We compared the two exports structurally, replacing every
  name, level and expression by a hash of its structure so that the numbering of entries does not matter: of their 34,119
  declarations, 34,117 were identical in every field, and the other two, the two theorems, had identical types and
  differing values, the difference being the line numbers in their `sorry` labels (31 and 39 against 30 and 38). With the
  line count kept, the export of the published challenge is byte-identical to the checked one's (section 1, statements).
- **The 41 vendored `CN1` modules are the already-published copies**, byte-identical to `../../formalization/CN1/`; no vendored
  file differs from those at all. The run of record used the first proof's verified copies, which differ from the published
  ones in comments only, and the export identity below is the proof that the closure is unchanged by the substitution. The
  first proof's challenge library, vendored in the run of record for a regression check, is not included here, because
  nothing in this proof uses it.
- **The published controls are the three tampered statements**, `HCNNegControls.Tamper.Move163`, `.DropSquarefree` and
  `.Swap431`, regenerated by the published `../certificates/gen_controls.py`. Their statements are the run of record's,
  byte for byte, and so are their exports (section 1, statement closures).
- **Three checked files are not published:** the proof-side controls that prove the theorems through a postulated false bound,
  through a postulated threshold, and with one certificate step replaced by `sorry`. As for the other entries, a file that
  declares a false axiom, or replaces a step of a proof by `sorry`, does not belong in a public library (the challenge and the
  tampered statements are statements left as `sorry` by design, as Comparator requires). Nothing else imports them.
- **The build configuration is replaced by a public one.** The checked tree's `lakefile.lean` required openai/math as a path
  dependency on a local checkout of commit `adc7f124`, with a shared `packagesDir`, and its manifest recorded openai/math as a
  path package. The public `lakefile.lean` requires openai/math from git at that commit, as `../../formalization/` does, has
  no `packagesDir`, and declares the four libraries above; its comments are new. `lake-manifest.json` is
  `../../formalization/lake-manifest.json` with the project name changed: the same 43 packages at the same revisions as the checked tree's manifest. `lean-toolchain` is unchanged
  (`leanprover/lean4:v4.34.1`), and `scripts/apply_oai_patches.sh` is the first proof's, byte for byte.

### How we checked it

**On the text.** The determinant route's [`strip_comments_compare.py`](../../determinant/formalization/scripts/strip_comments_compare.py)
removes comments and docstrings from every module of two trees and compares what is left, with whitespace collapsed. Run against
the checked tree, it reports all 79 published modules `SAME`; the files present only in the checked tree are the first proof's
challenge library and the three unpublished controls.

**On the compiled declarations.** We built both trees from source, side by side, in scratch copies against the same package
directory (the one the run of record used, with openai/math at `adc7f124` and its patched dependencies):

1. **The checked tree (A)**: a copy of the frozen sources with their original lakefile and manifest.
2. **The published tree (B)**: a copy of this directory, with the checked tree's lakefile and manifest in place of the public
   ones, so that both builds use the same compiled packages. The only differences between A and B are then the module sources.

Each tree was built with `lake build HCN CN1` (exit 0; 11,946 jobs; all 75 modules of `HCN` and `CN1` compiled from source in
each). Then, in each:

- **lean4export** (version 3.1.0, the binary Comparator used in the run of record, md5 `b8b81a76f7622ddc89d0c55ebe1382cc`)
  exported both theorems and their entire dependency closure, starting from `HCN.Main`:
  `lake env lean4export HCN.Main -- HCN.classNumber_le_two_iff HCN.classNumber_eq_two_iff`. This is the export that Comparator's
  kernels replay. It contains every declaration's name, universe parameters, type and value, but no docstrings. We made it twice:
  in the default form, and with `--export-mdata`, which also keeps the metadata annotations inside expressions.
- **A constant-hash listing**, the determinant route's `ConstHashes.lean` with its imports changed to every module of `HCN` and
  `CN1`, listed every constant declared in those modules (7,567 of them, including declarations the theorems do not use and the
  auxiliary declarations Lean generates) with its kind, universe parameters, and the structural hashes of its type and value.

The results:

| Output | Tree A (checked) | Tree B (published) | Comparison |
|---|---|---|---|
| lean4export, closure of both theorems | md5 `22a3868d30e60d350092b0029767a2eb`, 1,812,089,180 bytes | md5 `22a3868d30e60d350092b0029767a2eb`, 1,812,089,180 bytes | byte-identical |
| the same, with `--export-mdata` | md5 `6598d1d2e74b3567147c0b97ef991880`, 1,818,728,606 bytes | md5 `6598d1d2e74b3567147c0b97ef991880`, 1,818,728,606 bytes | byte-identical |
| constant hashes, all 7,567 `HCN` and `CN1` constants | md5 `a749bd965db0b34a7bc924a6aaf31f53`, 658,904 bytes | md5 `a749bd965db0b34a7bc924a6aaf31f53`, 658,904 bytes | byte-identical |

So the published modules compile to the same declarations, term for term, as the modules of the run of record, and the closure
that Comparator checked is the closure of the published theorems. Tree B was built and compared three times: first, again after
the `Threshold` docstring correction (which rebuilt `HCN.Numerics.Threshold`, `HCN.Assembly.LowerBound`, `HCN.Assembly` and
`HCN.Main`), and a third time, rebuilt from scratch from the final sources (`lake build HCN CN1 HCNChallenges HCNNegControls`,
exit 0, 11,952 jobs); all three results were the same every time. Docstrings enter neither export: the two
`--export-mdata` exports are identical although the docstrings of A and B differ.

The export also gives an independent count of that closure: 108,547 theorems, 22,281 definitions, 1,473 inductive types (with
1,598 constructors and 1,475 recursors), 54 opaque constants, 4 quotient constants and exactly 3 axioms, `propext`, `Quot.sound`
and `Classical.choice`. That is 135,435 constants, the same count, kind by kind, as the closure audit of the run of record.

**A control for the method.** In a third copy (C) of the published tree, the proof of `HCN.Finite.NotRep.sound` was given one
extra, unused line, `have _h : (1 : ℕ) = 1 := rfl`, which leaves its statement alone and changes its proof term. After a rebuild
(exit 0), both comparisons with the checked tree failed, as they should: the export differed (md5
`b96a4d794aa487cd6576366776b1606f`, 1,812,072,443 bytes), and the constant-hash listing differed in exactly one line, the value
hash of `HCN.Finite.NotRep.sound`, with its type hash unchanged.

**The statements.** Comparator compares the theorems' statements in the challenge with those in the solution, so the published
challenge and the published tampered statements must also be the checked ones. We exported, in A and in B, each statement
module with both theorem names: `lake env lean4export <module> -- HCN.classNumber_le_two_iff HCN.classNumber_eq_two_iff`, which
gives the statements, their `sorry` proofs and their whole Mathlib closure.

| Statement module | default export, A = B | with `--export-mdata`, A = B | Comparison |
|---|---|---|---|
| `HCNChallenges.ClassNumberLeTwo` | md5 `afd206cc51cd352c3dc004d14ab72410`, 213,975,946 bytes | md5 `b15e635494074ba76927dafb9fa651dc`, 214,632,181 bytes | byte-identical |
| `HCNNegControls.Tamper.Move163` | md5 `221423ba3d75b9a11fc8b87f0ac1cf3a`, 213,977,131 bytes | md5 `7c27486f64539df6e3779ce457971085`, 214,633,366 bytes | byte-identical |
| `HCNNegControls.Tamper.DropSquarefree` | md5 `4d6ae9edff18501b0b9e241f6a0ba6b8`, 213,974,919 bytes | md5 `0899b873eeefd71f5939b30ecff7e07b`, 214,631,174 bytes | byte-identical |
| `HCNNegControls.Tamper.Swap431` | md5 `ce637c0b557791e3f14af91ece9e9b1d`, 213,976,133 bytes | md5 `8d98a4eb0aed5dc3f663bd8be9d45e74`, 214,632,368 bytes | byte-identical |

These are the results for the final sources; the tampered statements gave the same md5s in two rebuilds of B. In A, the
challenge and the tampered statements are the run of record's files; in B they are the published ones, the tampered
statements as regenerated by the published `../certificates/gen_controls.py`. In the sources, too, the tampered statements are
byte-identical to the run of record's from their first `theorem` on; only their header comments differ.

## 2. The generators and the data reproduce what is checked in

- **The original generators**, run unmodified in a sandbox that held a copy of the checked tree and the data, reproduced all 27
  generated files of the checked tree byte for byte: the 24 published ones and the three unpublished proof-side controls.
- **The published generators** in [`../certificates/`](../certificates/README.md) differ from the originals in their paths, their
  comments and docstrings, the header lines they write into the Lean files, and the names of their own negative-control files;
  the arithmetic is unchanged. `../certificates/regenerate_and_diff.sh` runs them in order and finds all 24 generated files
  byte-identical to the ones here: `ALL OK (24 generated files)`.
- **The class-number data** in `../certificates/data/` was re-computed by the programs that produced it, and each file was
  reproduced byte for byte: PARI/GP 2.17.4 (`gp_classno.gp`, d ≤ 300,000), the reduced-form count with and without Dirichlet's
  formula (`hcn_classno.c`, d ≤ 300,000 and d ≤ 340,000), and the separately written reduced-form count
  (`independent_classno.c`, d ≤ 340,000).

## 3. A fresh build from the public lakefile

We copied this directory, without any build state, into an empty scratch directory, with an empty Mathlib cache directory
(`MATHLIB_CACHE_DIR`), and followed the README, then ran the workflow's checks. The machine was an Apple M3 Ultra (32 cores,
96 GB of memory) under macOS 26. The copy was made before three comment-only changes: the `Threshold` docstring correction,
the final wording of the challenge's module docstring (one line longer than in this copy, which is why the warnings below sit
one line higher than in the published file), and the new comments of `lakefile.lean`. Its other files are the published ones,
except `VERIFICATION.md` itself, the sorry fixtures (made afterwards, from this build's logs) and the one-line fix to
`scripts/check_no_sorry.sh` described in section 5. After those changes we synced the copy to the sources and built it
again (table below, last rows), which recompiled exactly the changed modules and their dependents. The last comment-only edits
(section 4, run 1) came after that; the final sources were rebuilt from scratch in tree B of section 1.

| Step | Result |
|---|---|
| `scripts/apply_oai_patches.sh` | exit 0, 238 s wall (cloning the 43 packages): "OK: all packages at their pinned revisions, all 23 patches applied and verified." |
| `lake exe cache get` | exit 0, 90 s wall; 8,908 Mathlib files |
| `lake build HCN CN1 HCNChallenges` | exit 0, **"Build completed successfully (11948 jobs)."**, 3,686 s wall (61 minutes), 9,088 s user CPU |
| `lake build HCNNegControls` | exit 0, 8,927 jobs; the six expected `sorry` warnings of the three tampered statements |
| `scripts/check_no_sorry.sh` on the build log | OK: exactly the two challenge warnings, `HCNChallenges/ClassNumberLeTwo.lean:26:8` and `:34:8` |
| the axiom check of the README, importing `HCN.Main` only | exit 0; Lean's output was exactly the two lines below, and Lake's 23 "local changes" warnings went to standard error |
| `scripts/check_axioms.sh` on that output | "OK: HCN.classNumber_le_two_iff and HCN.classNumber_eq_two_iff depend only on standard axioms" |
| `scripts/apply_oai_patches.sh --check` afterwards | exit 0, all 23 patches still verified |
| after the docstring changes: `lake build HCN CN1 HCNChallenges` again | exit 0, 11,948 jobs; recompiled `HCN.Numerics.Threshold`, `HCN.Assembly.LowerBound`, `HCN.Assembly`, `HCN.Main` and `HCNChallenges.ClassNumberLeTwo` |
| `scripts/check_no_sorry.sh` on that log | OK: `HCNChallenges/ClassNumberLeTwo.lean:27:8` and `:35:8` |
| the axiom check and `scripts/check_axioms.sh` again | the same two lines; OK |

```
'HCN.classNumber_le_two_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'HCN.classNumber_eq_two_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Two things matter for anyone repeating this on a smaller machine. The package directory takes 22 GB (7.2 GB of it Mathlib's,
14.5 GB openai/math's compiled files), and the project's own build adds 0.6 GB. And one generated module needs a lot of memory:
`HCN.Assembly.Range` reached a peak resident set of 26.5 GB when compiled on its own (124 s), against about 5.9 GB for a
certificate chunk; it was also the slowest module of the build. The workflow in `.github/workflows/hcn.yml` therefore frees
disk space and adds a swap file before it builds. **The workflow has not yet run on GitHub**: whether a standard runner
builds `HCN.Assembly.Range` in time is untested, and the first run, with its date, runner, wall time and that module's peak
memory, will be recorded here.

## 4. Comparator on the published files

After the equivalence builds we ran Comparator again, on the published files themselves: the published challenge against the
published `HCN.Main`, and the three published tampered statements against it. The setup was the run of record's: Comparator
built at tag v4.34.0 (md5 `57b65af925cc7119b47a5622ff66fe3e`), its `lean4export` 3.1.0 (`b8b81a76f7622ddc89d0c55ebe1382cc`),
nanoda (`f6268f7adadedf28d3bb66bef7cc1810`), and a pass-through shim in place of landrun (`e9a9f8e2aef39eba07cd02705570e48f`),
so these runs, too, were **not sandboxed**. Each ran `lake env comparator comparator/<config>.json` with the configurations in
[`comparator/`](comparator), which permit only `propext`, `Quot.sound` and `Classical.choice`, with nanoda switched on.

We ran the set twice:
- **Run 1**, in the fresh copy of section 3, with the public lakefile, synced to the sources as they were before the last
  comment-only edits (the challenge's pointer to the first proof's challenge, and the three stale remarks of section 1).
- **Run 2**, on the final sources (challenge md5 `00b03da302cae50b565b0c80380f4afc`, `HCN/Main.lean` md5
  `866ee907b7c129a24c09a198977937b4`), in tree B of section 1, that is with the checked tree's build configuration.

Between them, the two runs cover the public build configuration and the final sources. Comparator's view of a challenge is
its export, and the final challenge's export is byte-identical to the checked challenge's (section 1).

| Configuration | Expected (the run of record's line) | Observed, both runs | Exit | Wall time, run 1 / run 2 |
|---|---|---|---|---|
| `ClassNumberLeTwo.json` | "nanoda kernel accepts the solution", "Lean default kernel accepts the solution", "Your solution is okay!" | the same three lines | 0 | 670 s / 639 s |
| `Tamper_Move163.json` | "Challenge and solution theorem statement do not match: 'HCN.classNumber_eq_two_iff'" | the same | 1 | 204 s / 192 s |
| `Tamper_DropSquarefree.json` | "Challenge and solution theorem statement do not match: 'HCN.classNumber_le_two_iff'" | the same | 1 | 204 s / 186 s |
| `Tamper_Swap431.json` | "Challenge and solution theorem statement do not match: 'HCN.classNumber_le_two_iff'" | the same | 1 | 207 s / 197 s |

An earlier accepting run in the fresh copy, on the version of the challenge whose docstring was one line shorter, gave the same
three lines (664 s).

## 5. The check scripts

[`scripts/check_axioms.sh`](scripts/check_axioms.sh) and [`scripts/check_no_sorry.sh`](scripts/check_no_sorry.sh) are the
determinant route's strict checks, adapted to two theorems. The axiom check requires the whole of Lean's output, with
whitespace removed, to be the two reports, in order, in which every entry is one of `propext`, `Classical.choice` and
`Quot.sound`; the sorry check requires a successful build with exactly the two challenge warnings. [`scripts/test_checks.sh`](scripts/test_checks.sh)
runs both over the fixtures in [`scripts/fixtures/`](scripts/fixtures), and over a missing file.
All 61 cases behave as expected: 35 for the axiom check (5 accept, 29 reject and a missing file) and 26 for the sorry check
(3 accept, 22 reject and a missing file). The axiom check is slightly stricter than the determinant route's: the file name in
the optional `info:` prefix may contain neither a quote nor a colon, so the prefix cannot swallow an `error:` line. Two
fixtures, made by the independent review, show the difference: with an `error:` line before or between the reports, behind an
`info:` prefix, the looser pattern accepts and this one rejects. Plain `lake env lean` never prints that prefix. The sorry fixtures whose names begin with `real_` are the log of the fresh build
above, the log of its rebuild from the final sources, and the log of the build of the three tampered statements, with Lake's progress lines and its "local changes" warnings (which
name the scratch directory) removed; the others are made from the fresh log by adding, removing or changing lines. Writing them
found one gap in our first version of `check_no_sorry.sh`: a log in which one challenge warning was printed twice, once with a
leading `./`, counted as two positions. The script now drops a leading `./` before it compares positions.
