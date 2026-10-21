# Experiment: Tier-1 First-Class Emitters (2026-08-18)

Managed research program to raise Telperion's SOS / transcendental-bracket /
p-adic certificate capabilities from one-off *demonstrators* to first-class,
pipeline-enforced *emitters + families*.

## 1. Motivation / prior state

Three certificate capabilities already produce kernel-checked Lean in the
`telperion-production` CI gate, but each bypasses the enforced
`certify() -> emit() -> freeze()` pipeline and its honesty machinery:

| Capability | Prior state | Defect |
|---|---|---|
| SOS/SDP (`sos_sdp.py`) | standalone `lean_certificate()` string builder; 1-theorem `∀ x y` frozen demo | no input-hash provenance, no honesty pins, non-canonical (`sstr`) ordering, not an `Emitter`, not a family |
| exp-bracket (`examples/exp_bracket`) | one-off `CustomAssemblyEmitter` template for a single constant | no reusable transcendental-bracket emitter; one instance |
| p-adic (`examples/padic_valuation`) | hand-assembled `ValuationFact` block via `CustomAssemblyEmitter` | not a first-class emitter; 4 facts, not a grid family |

## 2. Hypotheses

- **H1 (feasibility).** Each capability can be promoted to a first-class
  `Emitter` + `family.kind` path + convenience constructor, flowing through the
  single enforced `certify()`/`emit()`/`freeze()` API, without weakening the
  trust model.
- **H2 (honesty preserved).** Each arm carries a working *negative control*: it
  refuses out-of-class input at certification, and (where ties are declared)
  refuses an over-claiming certificate — proving the honesty gate is live, not
  decorative.
- **H3 (byte-stability).** Emitted Lean is byte-identical on regeneration across
  the sympy CI matrix (canonical graded-lex ordering, not sympy print order).

## 3. Arms (independent; SOS is the reference implementation)

Fixed shared foundation (owned centrally, not by arms):
`family.py` (new optional fields + `kind` + `__post_init__`), `certify.py`
(new `CertifiedInstance` fields + kind dispatch), `provenance.py`
(`family_hash` per-kind serialization), `__init__.py` (exports).

Each arm owns disjoint files — no cross-arm collision:

| Arm | Module (new) | Example (rewrite) | Test (new) |
|---|---|---|---|
| SOS (reference) | `src/telperion/emit_sos.py` | `examples/sos_sdp/generate.py` | `tests/test_sos_emitter.py` |
| Bracket | `src/telperion/emit_bracket.py` | `examples/exp_bracket/generate.py` (+ new `examples/log_bracket/`) | `tests/test_bracket_emitter.py` |
| p-adic | `src/telperion/emit_padic.py` | `examples/padic_valuation/generate.py` | `tests/test_padic_emitter.py` |

### Fixed interface contract (arms implement exactly these names)

- SOS: `class SOSEmitter(Emitter)` (`kind="sos_sdp"`); `def certify_sos_point(family, pt, name) -> tuple[CertifiedInstance, int]`; `def sos_family(...) -> InequalityFamily`.
- Bracket: `class IntervalBracketEmitter(Emitter)` (`kind="interval_bracket"`); `@dataclass(frozen=True) class BracketSpec`; `def certify_bracket_point(family, pt, name) -> tuple[CertifiedInstance, int]`; `def bracket_family(...) -> InequalityFamily`.
- p-adic: `class PadicValuationEmitter(Emitter)` (`kind="valuation"`); `def certify_valuation_point(family, pt, name) -> tuple[CertifiedInstance, int]`; `def valuation_family(...) -> InequalityFamily`.

`family.kind` gains `"sos"` (target + `sos_half_deg`), `"bracket"` (`bracket`
callable), `"valuation"` (`valuation_facts` callable). `certify()` dispatches
each to the arm's `certify_*_point`.

## 4. Methods / measurements (data collected per arm)

1. `certify(fam)` -> `emit(...)` -> `freeze(...)` -> `diff_frozen(...)` green.
2. `pytest tests/test_<arm>_emitter.py` green (exact-arithmetic self-checks).
3. `python examples/<fam>/generate.py --check` byte-stable (drift net).
4. **Negative control A (refusal):** an out-of-class target/fact raises
   `CertificationError` — recorded as a passing control.
5. **Negative control B (overclaim):** a declared tie the certificate does not
   achieve raises — recorded as a passing control.
6. `n_theorems`, `n_checks`, LOC, and lint-cleanliness (empty-binder guard).

## 5. Constraints (hard)

- **No local `lake build`** (SoC-watchdog hardware fault + standing order:
  Lean verification is GitHub Actions only). The Lean kernel verdict is
  CI-side; the in-session terminal state is Python-green + byte-stable +
  gate-wired. No arm may *claim* its Lean compiles locally.
- **Honesty discipline.** `conjecture1_proved=False` is untouched. No arm claims
  to close a research-open problem: SOS does **not** claim the dual "lands on
  s=5" for the recursive matching functional; bracket does **not** claim the g1
  `Real.log` bridge; p-adic ships the 23-adic *primitives*, not the crux.
  Module docstrings carry the scope banner.
- **Emission-affecting change => version bump** 0.1.3 -> 0.1.4; all three
  families refrozen; every emitter declares `requires_prelude`.
- Commit only when the operator asks.

## 6. Analysis plan

Per-arm PASS iff (1)-(3) green and both negative controls (4)-(5) fire.
Program PASS iff all three arms PASS, the full suite stays green, and an
adversarial honesty review finds no overclaim / empty-binder / stub. Residuals
and any arm that lands QUALIFIED (e.g. control missing) are reported honestly.

## 7. Deliverable

Conclusions presented for operator review: what is now first-class and
gate-ready, the measured data table, negative-control outcomes, the honesty
audit, and the explicit CI-side residual (kernel verdict pending push).
