# The tenth discriminant

This repository is our attempt at Terence Tao's
[experimental AI-math challenge](https://terrytao.wordpress.com/2026/10/20/an-experimental-ai-math-challenge-using-tenth-discriminant-bounds-to-explore-arguments-ruling-out-siegel-zeroes/)
of 20 October 2026: take one of the new arguments ruling out Siegel zeroes, and use it to bound a hypothetical tenth imaginary
quadratic field of class number one, without Heegner's method.

Our aim is a little more than a bound. We want a **kernel-checked** proof, in Lean 4, of the class number one theorem itself: the
imaginary quadratic fields ℚ(√−m) of class number one are exactly those with m ∈ {1, 2, 3, 7, 11, 19, 43, 67, 163}. The proof is to
go through the new zero-free region for Dirichlet L-functions rather than through Heegner, Baker or Stark. We also want that proof
to be readable by a number theorist, with one Lean lemma per step of the human argument and a short write-up alongside.

**Status: work in progress. Nothing in this repository is yet a finished proof.** The sections below say exactly what is done and
what is not.

## The argument in six steps

The route below was worked out in the comments of Tao's post. We are formalizing it; we did not invent it, and the credits section
says where each piece comes from. Write K = ℚ(√−m) and d = |disc K|, so d = m when m ≡ 3 (mod 4) and d = 4m otherwise. Let χ be the
real character attached to K.

1. If K has class number one (and m ≠ 1, 3), every ideal of its ring of integers is principal and the only units are ±1. So the
   Dedekind zeta function is half an Epstein zeta function: ζ_K(s) = ½ Σ′ Q(x, y)^{−s}, where Q is the principal form x² + xy +
   ((d + 1)/4)y², or x² + (d/4)y².
2. ζ_K(s) = ζ(s)·L(s, χ).
3. The Chowla–Selberg formula continues ½ Σ′ Q^{−s} past Re s = 1: it equals ζ(2s) + 2^{2s−1}√π Γ(s − ½)/Γ(s) d^{½−s} ζ(2s − 1),
   plus a K-Bessel series of size about e^{−π√d}.
4. At s = 7/8 the main part is ζ(7/4) + C·d^{−3/8}·ζ(3/4), where C = 2^{3/4}√π Γ(3/8)/Γ(7/8) ≈ 6.4847, and ζ(3/4) < 0, so it
   increases with d. It is negative at d = 652 and positive for every d ≥ 655; its zero is at d* = 653.98763…. *(Status: certified
   numerically in ball arithmetic, see `computations/`; not yet proved in Lean, and the Bessel remainder is bounded there using a
   standard inequality not yet proved here.)*
5. ζ(7/8) < 0, so for large d, L(7/8, χ) = ζ_K(7/8)/ζ(7/8) < 0. But L(σ, χ) > 0 for σ > 1. By the theorem that no Dirichlet
   L-function vanishes when Re s > 7/8 (apart from the pole of the trivial character at s = 1), L has no zero on (7/8, 1], so by
   continuity L(7/8, χ) ≥ 0. That is a contradiction, so **d ≤ 652**. *(Status: the argument is standard; the conclusion rests on
   step 4, so it is not yet proved here.)*
6. The finite range: if some prime p < (d + 1)/4 splits in K, a prime ideal of norm p would be principal, forcing Q(x, y) = p, which
   is impossible for such a small p. So K does not have class number one. *(Status: a computation finds such a witness prime for
   every non-Heegner field in range; it is not yet in `certificates/` or checked by the kernel.)*

## What is done today

- `computations/`: an independent recomputation of step 4, in mpmath at 50 digits (`cs_threshold.py`) and in Arb ball arithmetic at
  256 bits (`arb_threshold.py`). The values M(652) = −0.0022412 < 0 and M(655) = +0.0011379 > 0 are certified as balls. Two inputs
  of the remainder estimate are still standard facts we have not yet proved here: a K-Bessel inequality and a tail bound. The
  Lean version will replace them with a proved bound.
- `telperion/`: a vendored copy of the Telperion certificate engine (see below). It is the same snapshot that ships with our
  [Brualdi–Goldwasser repository](https://github.com/DrMurphyIsIn/brualdi-goldwasser).

## What is not done yet

- The Lean formalization (`formalization/`). Its first step is a one-screen statement using only Mathlib definitions, reviewed
  before any proof is built on it.
- The certificate generators for the numerical inequalities, and the witness primes (`certificates/`).
- The human-readable write-up (`notes/`).

When the proof is finished it will be checked by Comparator with two independent kernels (Lean's and nanoda). Only the three
standard axioms will be allowed, with no `sorry` and no `native_decide`. A deliberately tampered statement must be rejected. The
dependency closure will be audited for any class-number-one input.

## Trust base

The deep analytic input is the theorem that every Dirichlet L-function is non-zero for Re s > 7/8 (apart from the pole at s = 1),
from [openai/math](https://github.com/openai/math) (family 003, Apache-2.0). It is an unrefereed preprint, with a Lean proof. Once
our formalization exists, that proof will sit inside its checked dependency closure, so it will not be something a reader has to
trust. We replayed its Comparator challenge with both kernels (Lean's and nanoda) on 7 October 2026, locally and without
Comparator's sandbox. What a reader does have to trust is the statement (and the Mathlib definitions it uses), the kernels, and the
three standard axioms.

## Why Telperion

[Telperion](telperion/README.md) turns untrusted input (numbers, enclosures, witnesses and proof drafts, very often produced by a
language model) into Lean 4 certificates, which only the Lean kernel accepts or rejects. A hallucinated bound does not become a
theorem: it fails to check. What remains is the risk that the *statement* says the wrong thing, which is why the statement comes
first and is reviewed before any proof is built on it. Negative controls (deliberately wrong inputs that must be rejected) are part
of the pipeline. Independent audits, including known-answer tests, have caught real soundness bugs in our own tools, which were
fixed and disclosed (Arda #739, #740). We think this is one practical answer to the question Tao and others have been raising:
how to get the benefit of AI assistance in mathematics without trusting what the AI says.

*Note on the vendored copy:* `telperion/` is the same v0.1.6 snapshot that ships with our Brualdi–Goldwasser repository, and it
**predates those fixes**: its `arb_dh` winding-number routine samples the boundary rather than certifying it, and the
`emit_baez_duarte` emitter is still present. This project uses neither component. A newer snapshot will replace it.

## Credits

- The quasi-Riemann hypothesis at 7/8 for all Dirichlet L-functions: OpenAI, openai/math, family 003.
- The non-existence of Siegel zeroes and its digests: OpenAI; W. D. Banks (arXiv:2610.15483); B. Kerr (arXiv:2610.21099); B. Green.
- The Chowla–Selberg formula: S. Chowla and A. Selberg. Its use at s = 7/8 for this challenge, and the finite step (a
  Rabinowitsch-style criterion), were developed in the comments of Tao's post. We will credit the commenters by name once we have
  checked the thread at source.
- The challenge: T. Tao.

## AI use

This work is done with extensive use of AI assistance (Anthropic's Claude), in several separate sessions: one does the work and
another independently reviews it. Our aim is that every claim here is either machine-checked or labelled with how it was obtained;
while the work is in progress, the labels on steps 4–6 above say what is and is not yet checked.

## Licensing

The mathematics (Lean, generators, frozen certificates, scripts) is Apache-2.0, and the documents are CC-BY-4.0. `telperion/` is
under the Business Source License 1.1, which permits research, teaching, review and evaluation outright. See
[LICENSING.md](LICENSING.md).
