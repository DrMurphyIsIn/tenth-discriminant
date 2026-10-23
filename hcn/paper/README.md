# The paper: class number two

This folder holds the paper for the third entry in this repository: a kernel-checked Lean 4 proof that the imaginary quadratic
fields of class number at most two are exactly the 27 known ones, and those of class number two exactly the eighteen. It
extends the first paper's route (in `paper/` at the top of the repository) from one ideal class to every class.

- `paper.tex` is the source, and `paper.pdf` is the built paper (26 pages, including the references).
- `refs.bib` is the bibliography.
- The paper is archived as a version of the tenth-discriminant Zenodo record, DOI
  [10.5281/zenodo.23578359](https://doi.org/10.5281/zenodo.23578359) (reserved, not yet published). The DOI for all versions
  of the record is [10.5281/zenodo.23550257](https://doi.org/10.5281/zenodo.23550257).

## What the paper says

The theorem is classical: Baker and Stark solved the class number two problem in 1971. What the paper adds is a proof by the
first entry's route, and its formalization. The Dedekind zeta function of K splits into one Epstein zeta function per ideal
class; the Chowla–Selberg formula, proved for every positive definite form with an explicit remainder bound, continues each of
them to s = 7/8; and OpenAI's theorem that no Dirichlet L-function vanishes when Re s > 7/8 then shows that class number at
most two forces d ≤ 4777. Below that bound, short certificates built from the principal norm form show class number at least
three for the 1,429 other fields, explicit ideal witnesses show class number two for the eighteen, and the first proof's
theorem gives the nine of class number one.

The proof does not use Heegner's method (no j-invariant or singular moduli occur in its closure), linear forms in logarithms,
or the Gross–Zagier formula. It does use modular objects, and the paper says which: the Jacobi theta function and its
modular transformation, and, through OpenAI's proof of the 7/8 theorem, non-holomorphic Eisenstein series.

## Credit

The challenge is Terence Tao's, and the deep input is OpenAI's 7/8 theorem with its Lean proof. The extension of the
Chowla–Selberg argument to all class numbers, through the Epstein zeta functions of all the classes, is LemmaLab's, posted in
the comments of Tao's challenge; the analytic half of this proof is that extension, in the form that Mathlib and the first
proof make provable. The classical solution of the class number two problem is A. Baker's and H. M. Stark's. The paper gives
the credits in full (also in [`../README.md`](../README.md)), and records the AI use of everyone involved, ours included.

## How it was checked

The paper's verification section describes the run of record: Comparator accepted both theorems under nanoda and Lean's own
kernel (a local run, not sandboxed), a walk over the closure of 135,435 constants found only the three standard axioms, and
twelve recorded checks, ten of them controls that had to fail, printed their expected lines. A separate AI review session,
not a referee, replayed it. The published Lean files differ from the checked ones in comments and docstrings only, and give
a byte-identical export of the closure; [`../formalization/VERIFICATION.md`](../formalization/VERIFICATION.md) has the method,
the fresh build from the public lakefile, and a fresh Comparator run on the published files.

## Building it

You need a TeX distribution with `pdflatex` and `bibtex`:

```sh
pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper
```

Module paths in the paper are the public ones, under `hcn/formalization/` in this repository.
