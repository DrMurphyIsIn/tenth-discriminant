# Licensing

This repository uses a split licensing model.

## The mathematics: Apache-2.0 / CC-BY-4.0

Everything outside `telperion/` -- the Lean 4 formalizations (`formalization/`, `determinant/formalization/` and
`hcn/formalization/`), the certificate generators, their data and their frozen outputs (`certificates/`,
`determinant/certificates/` and `hcn/certificates/`), the scripts in `computations/`, the code, data and recorded outputs of the
fourth entry (`comparison/`), and the workflows in `.github/` -- is
licensed under the [Apache License 2.0](LICENSE). The documents (`notes/`, the papers in `paper/`, `determinant/paper/`,
`hcn/paper/` and `comparison/paper/`, the READMEs) are licensed under
[CC-BY-4.0](https://creativecommons.org/licenses/by/4.0/).

The mathematical content is unconditionally open. Lemmas suitable for Mathlib can be upstreamed
without friction (Mathlib requires Apache-2.0).

Emitted certificates (every `.lean` file a generator writes, and every `frozen/` record) are part of
the open mathematical record and are Apache-2.0, not BSL.

## The Telperion engine: Business Source License 1.1

`telperion/` is a vendored copy of the Telperion certificate engine, licensed under the
[Business Source License 1.1](telperion/LICENSE):

- **Free for research.** Academic research, teaching, scholarly work, peer review and evaluation are
  permitted outright by the Additional Use Grant.
- **Commercial production use** requires a license from the Licensor.
- **Change License:** each release converts to Apache-2.0 three years after its release date.
- Contributions to the engine require the individual CLA in [`telperion/CLA.md`](telperion/CLA.md).
  Contributions to the mathematics do not.

Reviewers do not need any license beyond the Additional Use Grant to regenerate and check every
certificate in this repository.
