# formalization/

This is the Lean 4 project. It proves `CN1.classNumber_eq_one_iff`, the class number one theorem for imaginary quadratic fields,
without Heegner, Baker or Stark. It is pinned to:
- Lean v4.34.1;
- openai/math at commit [`adc7f124`](https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a), which provides
  the zero-free region Re s > 7/8 for Dirichlet L-functions;
- the Mathlib revision that openai/math uses, d13f23b723b8a846827a245b89c10fc7d3f11612.

## The statement

[`CN1Challenges/ClassNumberOne.lean`](CN1Challenges/ClassNumberOne.lean) is the statement of record:

```lean
theorem CN1.classNumber_eq_one_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 1 ↔ m ∈ ({1, 2, 3, 7, 11, 19, 43, 67, 163} : Finset ℕ)
```

That file imports only Mathlib and, as Comparator requires, leaves the proof as `sorry`. The proof is the solution module
[`CN1/Main.lean`](CN1/Main.lean). The statement uses only Mathlib definitions (`NumberField`, `NumberField.classNumber`,
`Module.finrank`, `Squarefree`), so a reader can check what it says without reading any of our code. Every imaginary quadratic
field ℚ(√−m) satisfies the hypotheses, and the hypotheses force K ≅ ℚ(√−m). The small lemma
`CN1.Candidates.squarefree_ne_zero_and_not_isSquare_neg` in [`CN1Challenges/Candidates.lean`](CN1Challenges/Candidates.lean)
records the two facts behind that. The same file keeps the three candidate phrasings that were considered.

An independent AI review session checked the statement before the assembly that proves it was built. As part of that check it kernel-checked a
lemma of its own, not included here, that the hypotheses are satisfiable for every squarefree m. So the theorem is not vacuous.

## The modules, step by step

| Step of the argument | Module | Main declarations |
|---|---|---|
| Foundations: 𝓞_K = ℤ[ω], the norm form, the units | `CN1.Foundations.Basic` | `norm_int_eq_principalForm`, `coe_unit_eq_one_or_neg_one` |
| The Kronecker character χ₋d | `CN1.Foundations.Character` | `kroneckerChar`, `kroneckerChar_isQuadratic` |
| disc K = −d, splitting and ramification of primes | `CN1.Foundations.Discr`, `.Splitting`, `.Ramified` | `discr_eq`, `ncard_primesOver_eq_two_of_kroneckerChar_eq_one` |
| 1. h = 1 ⇒ ζ_K = ½ Σ′ Q^(−s) | `CN1.Epstein.Lattice` | `dedekindZeta_eq_half_latticeSum` |
| 2. ζ_K = ζ · L(·, χ) | `CN1.Epstein.IdealCount`, `.PrimePower`, `.Factorization` | `dedekindZeta_eq_riemannZeta_mul_LFunction` |
| 1 + 2 together | `CN1.Epstein.Epstein`, `.Bridge` | `epstein_identity`, `epstein_identity_Z` |
| 3. Chowla–Selberg with an explicit remainder, continued to s = 7/8 | `CN1.ChowlaSelberg.*` | `CS_main`, `norm_E_seven_eighths_le`, `CS_seven_eighths_zeta_mul` |
| 4. ζ(7/4), ζ(3/4), ζ(7/8), Γ(3/8)/Γ(7/8), and the threshold | `CN1.Numerics.*` | `riemannZeta_three_quarters`, `Gamma_ratio_enclosure`, `disc_le_652_of_CS` |
| 5. L(7/8, χ) ≥ 0, from OpenAI's zero-free region | `CN1.Assembly.Positivity` | `LFunction_seven_eighths_nonneg_of_isQuadratic` |
| 6. The finite range: 190 split-prime witnesses | `CN1.Finite.SplitPrime`, `.Witnesses`, `.Witnesses.Chunk1..4` | `classNumber_ne_one_of_witness`, `mem_nonHeegner190` |
| The nine fields have class number one (Minkowski) | `CN1.Finite.Converse` | `classNumber_eq_one_of_mem_nine` |
| Assembly | `CN1.Assembly.Core`, `CN1.Main` | `classNumber_eq_one_iff_of_epstein`, `CN1.classNumber_eq_one_iff` |

The only declaration from outside Mathlib and this project that our code cites directly is OpenAI's `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`,
in [`CN1/Assembly/Positivity.lean`](CN1/Assembly/Positivity.lean). Its proof, and everything it depends on, is part of the build and
of the checked closure.
[`CN1/Numerics/AxiomCheck.lean`](CN1/Numerics/AxiomCheck.lean) prints the axioms of the numerical lemmas. The files
`CN1/Finite/Witnesses*.lean` and `CN1/Numerics/ZetaTables.lean` are generated; their generators are in
[`../certificates/`](../certificates/README.md). [`../notes/proof.md`](../notes/proof.md) walks through every step with file and line
references.

## Building

You need [elan](https://github.com/leanprover/elan), git and Python 3. Run this from this directory:

```sh
scripts/apply_oai_patches.sh          # fetch the pinned packages and apply openai/math's patches (once)
lake exe cache get                    # download the Mathlib build cache
lake build CN1.Main CN1Challenges     # exactly what was verified; plain `lake build` builds CN1
```

**Why the script.** openai/math pins 42 packages and ships Lean-v4.34.1 compatibility patches for 23 of them
(`lean/patches/<package>-lean4341.patch`). Its lakefile applies them only when openai/math is the root project. When it is a
dependency, as here, the patches have to be applied by hand. [`scripts/apply_oai_patches.sh`](scripts/apply_oai_patches.sh) does
that and then verifies the result:
- every package is at its pinned revision;
- every patch is applied exactly;
- every untracked file is one the patch creates.

`scripts/apply_oai_patches.sh --check` verifies without changing anything. Afterwards, `lake build` warns that 23 repositories
"have local changes". That is expected: it is the patched state. **Do not run `lake update`**: it re-resolves the dependencies,
and openai/math's post-update hook fails in this layout.

These instructions were tested on a fresh clone. The script fetched all the packages and applied the patches, and the patched
state matched the one we checked exactly: for every patched package, the `git diff` against its pinned commit had the same md5.
A complete build from that fresh clone had not finished when v1.0.0 was archived. The result will be recorded here.

Building OpenAI's dependency closure is the expensive part. On our machine (Apple silicon), with the dependencies already built,
rebuilding this project's own modules took about 80 seconds and 6.8 GB of memory. A first build compiles several thousand modules
of openai/math and its dependencies.

## Checking with Comparator

[Comparator](https://github.com/leanprover/comparator) checks that a solution proves a separately written statement, using only
permitted axioms, and replays the proof through Lean's kernel and, optionally, through [nanoda](https://github.com/ammkrn/nanoda_lib),
an independent reimplementation of the kernel. The configurations are in [`comparator/`](comparator):

| Configuration | Challenge | Expected verdict |
|---|---|---|
| [`ClassNumberOne.json`](comparator/ClassNumberOne.json) | the statement of record | "Your solution is okay!" (nanoda and Lean's kernel both accept) |
| [`Tamper_DropSquarefree.json`](comparator/Tamper_DropSquarefree.json) | the statement without `Squarefree m` (false: m = 4) | rejected: "Challenge and solution theorem statement do not match" |
| [`Tamper_Nine167.json`](comparator/Tamper_Nine167.json) | 163 replaced by 167 (false: ℚ(√−167) has class number 11) | rejected: statement mismatch |

Each permits only `propext`, `Quot.sound` and `Classical.choice`, with nanoda switched on. To run them:
1. Build Comparator at tag v4.34.0 with toolchain v4.34.1, together with its `lean4export`, and build nanoda.
2. Set `COMPARATOR_LEAN4EXPORT` and `COMPARATOR_NANODA` to those binaries, and `COMPARATOR_LANDRUN` to landrun.
3. From this directory, run `lake env comparator comparator/<config>.json`.

landrun is Linux-only. Our runs were on macOS, with a pass-through shim in its place, so they were **not sandboxed**.

Our results on the Lean modules and configurations in this repository, built against the same patched dependency tree as the run
of record:
- the real configuration was accepted by both kernels;
- both tampered configurations were rejected: "Challenge and solution theorem statement do not match".

Two further negative controls, tampered *proofs* that use a false bound postulated as an axiom or closed with `sorry`, were run
against the same proof and rejected ("Illegal axiom detected"). They are not published.
