# paper/

The paper accompanying this repository: *The class number one theorem without Heegner, kernel-checked: d ≤ 652 from the 7/8
quasi-Riemann hypothesis in Lean 4* (Peter W. Murphy, October 2026, v1.0.0).

- `paper.tex`: the source. Lean declarations are cited by name and module (`formalization/CN1/...`), never by line number.
- `refs.bib`: the bibliography. Every entry was checked against Crossref, zbMATH, arXiv or the GitHub page it points to.
- `paper.pdf`: the built paper.

## Building

The paper uses `pdflatex` and `bibtex` (not biber), with the `amsplain` bibliography style. From this directory:

```sh
pdflatex paper && bibtex paper && pdflatex paper && pdflatex paper
```

The Lean listings render their Unicode through the `listings` package's literate table in the preamble; no special font is
needed. A TeX Live installation with `amsthm`, `cleveref`, `listings`, `tikz`, `booktabs`, `microtype` and `hyperref`
suffices (TeX Live 2025 basic was used).

## Licensing

The paper is CC-BY-4.0, like the other documents in this repository; see `../LICENSING.md`.
