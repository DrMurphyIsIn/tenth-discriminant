# Reviewing and contributing

Thank you for looking. Careful review is the most valuable contribution anyone can make.

## What most needs checking

The kernel checks every deduction in the Lean proof. What remains are questions about meaning:

1. **Does the formal statement say what the class number one theorem says?** It is in
   [`formalization/CN1Challenges/ClassNumberOne.lean`](formalization/CN1Challenges/ClassNumberOne.lean) and uses only Mathlib
   definitions.
2. **Are the numerical inputs proved about the real objects?** Every inequality about ζ and Γ must be stated about Mathlib's
   `riemannZeta` and `Gamma`, not about a stand-in.
3. **Is anything overstated?** The README and the paper separate what is machine-checked from what is not. Please tell us where
   they fail to.

## How to report

Open an issue. A short note saying "I read X and Y looks wrong" is enough.

## Licensing of contributions

Contributions to the mathematics (everything outside `telperion/`) are welcome under Apache-2.0 (code) and CC-BY-4.0 (documents),
with no agreement needed. Contributions to the Telperion engine in `telperion/` need the individual CLA in
[`telperion/CLA.md`](telperion/CLA.md).
