# Jensen-Polya Hyperbolicity: Status Document

**conjecture1_proved = False.** This document is an honest accounting of what
has been formally proved, what trust boundaries exist, and what has not been
done. Nothing here is a proof of the Riemann Hypothesis.

---

## What Is Proven

### Kernel-verified box-hyperbolicity for J^{2,n}, n = 0, 1, 2

The Lean 4 kernel (via `lake build`) has accepted, sorry-free, three theorems:

| Theorem | Jensen polynomial | Discriminant margin |
|---|---|---|
| `jensen_box_hyperbolic_deg2_0` | J^{2,0}(x) | approx 2.82e-04 |
| `jensen_box_hyperbolic_deg2_1` | J^{2,1}(x) | approx 2.27e-08 |
| `jensen_box_hyperbolic_deg2_2` | J^{2,2}(x) | approx 8.00e-13 |

Each theorem states: for every triple (c0, c1, c2) of real numbers lying in the
certified rational coefficient box, the degree-2 polynomial
`c2 * X^2 + c1 * X + c0` has exactly 2 real roots (counting multiplicity), i.e.,
`(Polynomial.C c2 * Polynomial.X^2 + Polynomial.C c1 * Polynomial.X + Polynomial.C c0).roots.card = 2`.

The Jensen polynomial J^{d,n}(x) = sum_{k=0}^{d} C(d,k) * alpha(n+k) * x^k, where
alpha(m) is the coefficient of t^{2m} in Xi(t) = xi(1/2 + it). For d=2:
c0 = alpha(n), c1 = 2*alpha(n+1), c2 = alpha(n+2). The three certs cover
n=0,1,2, needing alpha(0..4) -- all reachable via the rigorous acb_series path.

**Axioms.** Each theorem depends on exactly: `{propext, Classical.choice, Quot.sound}`.
No `native_decide`, no `sorry`, no `ofReduceBool`. Confirmed by `#print axioms`
in the emitted file, kernel-checked at build time.

**AXLE statement-match gate.** Each theorem is followed by a kernel-checked
`example` that closes the AXLE gate: the example compiles only if the emitted
Prop literally matches the intended box-hyperbolicity statement. A type mismatch
or proof of a weaker statement would cause a build failure.

**Proof structure.** The proof chains two steps:
1. A `nlinarith` box-positivity argument establishes `0 <= c1^2 - 4*c2*c0`
   (the discriminant lower bound) from the rational box constraints.
2. The Task-4 bridge lemma `hyperbolic_deg2_of_discrim_nonneg` (in
   `JensenBridge.lean`) concludes `.roots.card = 2` from the nonzero leading
   coefficient and nonnegative discriminant.

**This is the first formally kernel-verified Jensen-polynomial hyperbolicity
result for the Riemann zeta function** (to the authors' knowledge as of 2026-09-05).

---

## The Trust Boundary

The one non-kernel link in the chain is the **coefficient-membership claim**:
the assertion that the true value alpha(m) lies within the rational box [lo, hi].

This claim is certified by **Arb ball arithmetic** (python-flint), not by the
Lean kernel. For n = 0, 1, 2 (needing alpha(0..4)), the `acb_series` path
evaluates Xi(t) as a truncated power series in t using Arb's ball arithmetic
(every operation carries a rigorous, directed-rounded error ball). The ball's
outward rational endpoints give the certified [lo, hi].

This is the plan's one documented non-kernel input, analogous to the inputs R
and B in other Telperion certificate families. Everything downstream of the
rational box (the nlinarith discriminant argument and the bridge lemma
invocation) IS kernel-verified.

---

## What Is Not Done / Deferred

### (a) Coefficients alpha(m) for m >= 5 (needed for n >= 3): rigorous tail bound required

python-flint's `acb_series` zeta implementation returns at most 10 series terms
(indices 0..9), so alpha(m) for m >= 5 (series index 2m >= 10) is inaccessible
via the rigorous power-series path. A finite-evaluation extraction (evaluate
Xi(t) at a few points and solve a Vandermonde system) is NOT rigorous by itself:
the residual is
`rem_k = Xi(t_k) - sum_{j<m} alpha(j) t_k^{2j} = alpha(m) t_k^{2m} + alpha(m+1) t_k^{2(m+1)} + ... + [tail]`,
and any finite linear solve DROPS the higher-order tail `alpha(m+3)+`. That
truncation error (order 1e-28 at the evaluation points used) is many orders of
magnitude LARGER than the acb-ball input-propagation radius (order 1e-169), so a
solve that reports only the ball radius UNDERSTATES the true uncertainty and does
NOT provably contain alpha(m).

**A rigorous high-m coefficient requires a Cauchy truncation-tail bound**
`|alpha(k)| <= max_{|t|=R} |Xi(t)| / R^{2k}`
(from the Cauchy estimates for the Taylor coefficients of the entire function
Xi), added explicitly to the ball so the returned interval provably contains
alpha(m) including the dropped tail. This is **deferred to Phase 2**. Until then,
`enclose_coeff_box` raises `NotImplementedError` for any requested coefficient
with series index > 9, rather than silently producing an unsound enclosure.

Consequently the grid is J^{2,n} for **n = 0, 1, 2 only** (three certs). n=3
(which needs alpha(5)) is excluded to preserve the rigor guarantee. (The n=3
hyperbolicity conclusion is very likely still true -- the tail 1e-28 is far
below the n=3 Turan margin 1.5e-17 -- but it cannot be honestly certified with
the current tooling.)

### (b) Degrees d >= 3: deferred to Phase 2

Cubic (d=3) and higher-degree hyperbolicity certificates require a theorem of
the form "PSD Hermite-Bezoutian matrix implies all roots real." Mathlib (as of
2026-09-05) lacks the discriminant-to-real-roots bridges over R for degrees >= 3.

Phase 2 will implement a general **Hermite-Bezoutian PSD engine** that handles
all degrees d <= 8 uniformly via a single kernel-verified theorem. At that point,
the grid can be extended to (d, n) in {2,3,4,...} x {0,1,2,...} -- alongside the
Cauchy tail bound of item (a) for the high-m coefficients.

### (c) Uniform-in-d effective threshold N(d)

The actual RH-closing piece of the Jensen-Polya program requires showing that
J^{d,n} is hyperbolic for ALL n >= N(d) and all d (or for all n, d
simultaneously). This uniform threshold is a deep analytic result
(Griffin-Ono-Rolen-Zagier 2019 for existence; sharp bounds are open) and is
entirely out of scope for certificate-based formal verification with finite
rational boxes. The three certs here cover concrete small-n instances only.

### (d) Emitter framework integration

The current emitter (`JensenPolynomialHyperbolicityEmitter`) exposes only
`render_box` and is not yet registered as a first-class Telperion emitter with
`emit_body`/`certify.py` integration. This is a deferred capability follow-up.

---

## Summary Table

| Claim | Status |
|---|---|
| J^{2,n} hyperbolic for n=0,1,2 | KERNEL-VERIFIED (sorry-free, axioms clean) |
| Coefficient boxes (alpha(0..4)) certified | ARB-CERTIFIED (non-kernel, documented boundary) |
| alpha(m) for m >= 5 (n >= 3) | DEFERRED to Phase 2 (needs Cauchy tail bound) |
| d >= 3 hyperbolicity | DEFERRED to Phase 2 (Hermite-Bezoutian engine) |
| Uniform threshold N(d) | OUT OF SCOPE |
| Proof of RH | FALSE (conjecture1_proved = False) |
