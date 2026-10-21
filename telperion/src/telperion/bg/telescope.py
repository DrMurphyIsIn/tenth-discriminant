"""Telescoping closure over trees — Telperion's tree-induction vocabulary.

Many recursive inequalities have the shape "the sum of a per-node local term is
bounded", closed by a POTENTIAL P with a per-node super-solution inequality:

    local(v)  ≤  P(v) − Σ_{c ∈ children(v)} P(c)      (super-solution)
    ─────────────────────────────────────────────────────────────────
    Σ_{v ∈ tree} local(v)  ≤  P(root)                 (telescopes)

The sum telescopes because every node's P appears once as +P(v) (as the node)
and once as −P(v) (as a child of its parent), leaving only P(root).  This is the
Brualdi-Goldwasser ledger's shape (Σ growth ≤ tax = HypLedgerTelescope): FINDING
a closed-form P is the open wall, but the ASSEMBLY — per-node inequality ⟹ global
bound — is mechanical and reusable.  This module provides:

  * TELESCOPE_LEMMA: the rose-tree telescoping lemma in Lean, proved once
    (structural recursion + List.sum_le_sum), reusable for any (local, P);
  * per-node super-solution OBLIGATIONS: given a potential and per-class local
    terms, the finite family of rational inequalities to certify (Polya), each
    `local(class) ≤ P(cav) − Σ P(child cav)` — the certifiable pieces;
  * the exact-engine check that a candidate telescopes (dual to the Lean proof).

The Lean kernel is the arbiter; the potential is the user's (or the open crux's).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

# The reusable rose-tree telescoping lemma.  local_/P are arbitrary node
# functionals; the hypothesis is the per-node super-solution; the conclusion is
# the telescoped global bound.  Proved by structural recursion on the tree.
TELESCOPE_LEMMA = """/-- Finitely-branching (rose) trees, for telescoping tree inductions. -/
inductive RTree where
  | node : List RTree → RTree

/-- Sum of a node functional over every node of the tree. -/
def RTree.sumOver (loc : RTree → ℝ) : RTree → ℝ
  | .node cs => loc (.node cs) + (cs.map (RTree.sumOver loc)).sum

/-- Telescoping closure: a per-node super-solution `local + Σ_children P ≤ P`
    gives the telescoped global bound `Σ_nodes local ≤ P root`.  Every node's `P`
    cancels between its own term and its parent's child-sum, leaving `P root`. -/
theorem RTree.telescope {loc P : RTree → ℝ}
    (h : ∀ cs : List RTree, loc (.node cs) + (cs.map P).sum ≤ P (.node cs)) :
    ∀ t : RTree, RTree.sumOver loc t ≤ P t
  | .node cs => by
    have hchild : (cs.map (RTree.sumOver loc)).sum ≤ (cs.map P).sum :=
      List.sum_le_sum (by
        intro c hc
        exact RTree.telescope h c)
    have hnode := h cs
    simp only [RTree.sumOver]
    linarith
"""


@dataclass(frozen=True)
class TelescopeSpec:
    """A candidate telescoping closure: per-node classes with their local term
    and the potential evaluated at the node and its children.

    ``local_of`` and ``potential_of`` map a class descriptor to exact rationals
    (or sympy expressions in the cavity for symbolic classes).  ``children_of``
    yields the child potential values summed.  The obligation per class is
    ``local ≤ potential_node − Σ potential_children``.
    """

    name: str
    classes: Sequence[object]
    local_of: Callable[[object], object]
    potential_node_of: Callable[[object], object]
    potential_children_of: Callable[[object], Sequence[object]]

    def obligations(self):
        """Yield (class, slack) where slack = P_node - Σ P_child - local must be
        >= 0.  Feed each slack to the Polya certifier as a `0 <= slack` target."""
        for c in self.classes:
            slack = (self.potential_node_of(c)
                     - sum(self.potential_children_of(c))
                     - self.local_of(c))
            yield c, slack

    def check(self) -> bool:
        """Exact-engine dual: every super-solution obligation holds (slack >= 0).
        A False here means the candidate potential is NOT a super-solution -- the
        overclaim trap for telescoping (a P that doesn't telescope is refused)."""
        return all(slack >= 0 for _, slack in self.obligations())
