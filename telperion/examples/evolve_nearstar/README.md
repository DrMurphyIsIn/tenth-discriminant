# evolve_nearstar — a frozen evolve-discovered certificate

The milestone `docs/EVOLVE_RESULTS_2026-08-18.md` left open: an artifact produced
by the `telperion.evolve` search loop, emitted to Lean and frozen for the kernel
gate.

## What this is

`generate.py` runs the **structured, LLM-free** island loop
(`telperion.evolve.freeze.discover_nearstar_champion`, seed=0, deterministic) on
the near-star payload. It climbs from a failing seed genome to a certifying
champion:

```
ratio_src = 486/529 * (1 + 1/(4*s**2 + 11*s + 6))**11,  s0 = 0,  lift_max = 0
score = 1000  (exact-arithmetic certify tier),  evals = 344,  s* = 5
```

It then emits the champion's **reusable ratio certificate** — the Pólya-certified
decreasing step plus the crossing-of-1 facts — via `UnimodalMaxEmitter`, bundled
with the reusable `Telperion.unimodal_peak` prelude, into
`lean/EvolveNearStar.lean`.

## Trust model (unchanged)

The loop only **proposes**; the emitted theorems still face the identical kernel
gate. The generator is untrusted — a wrong certificate is a compile error, never
a false theorem.

## The two tiers, honestly

1. **Reproducible discovery + lint-clean emission** — verified locally and in CI
   by `tests/test_evolve_frozen.py` (seeded determinism, `certify`-tier success,
   soundness-lint clean). This is the part this machine can prove.
2. **Kernel green (`lake build`)** — cloud-gated. This machine does not build
   Lean. The near-star sequence `f` is not a rational function (only its
   *ratio* is), so — by `UnimodalMaxEmitter`'s design — the final `unimodal_peak`
   application against a concrete `f` is the caller's one line; the frozen file
   carries the reusable ratio certificate + prelude, ready to compile.

Regenerate (byte-identical for seed=0):

```bash
python examples/evolve_nearstar/generate.py
```
