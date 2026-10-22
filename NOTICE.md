# Notices

- **openai/math** (https://github.com/openai/math), Apache-2.0. The zero-free region Re s > 7/8 for Dirichlet L-functions
  (family 003, commit adc7f124) is a Lake dependency of `formalization/`. It is fetched at build time and is not vendored here.
  OpenAI's Lean-v4.34.1 compatibility patches for its dependencies are applied from openai/math's own `lean/patches/` directory by
  `formalization/scripts/apply_oai_patches.sh`; they are not copied here either.
- **The packages openai/math depends on**, at the revisions it pins (listed in `formalization/lake-manifest.json`), each under its
  own license. Besides Mathlib's own dependencies Batteries and Aesop, two of them appear in the checked dependency closure of our theorem:
  PrimeNumberTheoremAnd and RellichKondrachov.
- **Mathlib** (https://github.com/leanprover-community/mathlib4), Apache-2.0.
- **Comparator** (https://github.com/leanprover/comparator) and **nanoda** (https://github.com/ammkrn/nanoda_lib) were used to
  check the proof. They are not included here.
- **Telperion** (`telperion/`), Business Source License 1.1; see `telperion/LICENSE`. Snapshot of development commit `5b8eea03`
  (2026-10-18).
- The mathematical route is credited in the README (Credits) and in the paper.
