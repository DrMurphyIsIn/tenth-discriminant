"""Telescoping potentials: the per-node certificate layer of a global bound.

The origin campaign's central structural move (cavity_potential.py →
PotentialBound.lean): a global bound over a recursively-built object
telescopes into a PER-NODE inequality — find a potential P with the per-node
certificate and the global theorem follows by structural induction.  The full
shape has two halves:

1. **The per-node inequality family** — expressible in Telperion TODAY.
   `per_node_family` builds it: symbols are the children's cavity values
   m₁..m_k on a domain, the claim is the user's per-node inequality
   (typically  P(step(m₁..m_k)) ≤ Σ P(mᵢ) + local terms, spelled by the
   caller as a target), and the FIXED POINT of the step map is the natural
   tie — pin it (`ties=`) and the overclaim trap guards the telescoping's
   equality case, exactly as the origin's tie pinned P(3/23) = 0.

2. **The induction glue** — NOT emitted by the tool (it needs the user's Lean
   tree type and fold lemmas).  `INDUCTION_SKELETON` below is the documented
   CustomAssembly-style template: instantiate it with your tree recursor and
   the emitted per-node theorems close each case.  Making this half generic
   is the declared v2 headline (see CHANGELOG named-opens).
"""
from __future__ import annotations

import sympy as sp

from ..family import GridSpec, InequalityFamily

INDUCTION_SKELETON = """-- The telescoping induction (instantiate per your tree type; the per-node
-- theorems emitted by Telperion close each constructor case):
--
-- theorem global_bound : ∀ t : «TreeType», measure t ≤ bound t := by
--   intro t
--   induction t with
--   | leaf => «leaf_case»            -- the base per-node theorem
--   | node children ih =>
--       have hstep := «per_node_theorem» «cavity args of children»
--       «fold ih through hstep»      -- Σ-telescoping: linarith/calc over ih
"""


def fixed_points(step: sp.Expr, m: sp.Symbol):
    """Exact fixed points of a one-child step map m' = step(m) — the natural
    tie candidates of the telescoping (the origin: m* = 3/23)."""
    sols = sp.solve(sp.Eq(step, m), m)
    return [s for s in sols if s.is_number and s.is_real and s >= 0]


def per_node_family(
    name: str,
    arity: int,
    per_node_target,
    lean_name=None,
    cap: sp.Rational | None = None,
    ties=None,
    **kwargs,
) -> InequalityFamily:
    """The per-node inequality as a Telperion family.

    per_node_target(ms) -> expr: the claim 0 <= expr over the children's
    cavity symbols ms = (m1..m_arity), each nonnegative (and <= cap if given —
    encode the cap by substituting mᵢ = cap·σᵢ/(1+σᵢ) or by box families;
    v1 keeps the raw orthant and leaves domain restriction to the caller's
    spelling).  ties: substitution dicts (e.g. the step map's fixed point at
    every child) where the telescoping is exactly tight — STRONGLY
    recommended; an unpinned potential is exactly how the origin's three
    overclaims happened."""
    ms = sp.symbols(f"m1:{arity + 1}", nonnegative=True)
    return InequalityFamily(
        name=name,
        symbols=ms,
        grid=GridSpec([("node", [0])]),
        lean_name=lean_name or (lambda pt: f"{name.lower()}_per_node"),
        target=lambda pt: per_node_target(ms),
        ties=ties,
        **kwargs,
    )
