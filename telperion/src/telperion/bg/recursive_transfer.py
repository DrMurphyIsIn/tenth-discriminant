"""Recursive transfer factor: the multi-level lift, and why universal F <= 1 IS Brualdi-Goldwasser.

`mixed_block_martingale.py` handled ONE hub level.  This lifts the per-block transfer factor to the WHOLE
tree, recursively (blocks-of-blocks), and reports honestly on the universal bound `F_b <= 1`.

THE RECURSION (exact, verified `== rooted_phi.phi11_rooted` on all trees).  Root the tree; at each vertex
v with children c_1..c_j (each a sub-block) and a virtual parent edge,

    mu_v = 1 / (j + 1 + S),     S = sum_i mu_{c_i}          (the cavity message)
    a_v  = (j + 1 + S) / (j + 1) = 1 + S/(j+1)              (the vertex amplitude)
    F_v  = (64/621) * a_v^11 * prod_i F_{c_i}               (the transfer factor)

with leaves emitting `mu = 1`, `a = 1`, `F = 64/621`.  This is the ENTIRE rooted `Phi^11` as a two-quantity
per-vertex transfer -- the multi-level lift of the single-hub formula.  `F_root = Phi^11_rooted(T, root)`.

UNIVERSAL `F_b <= 1` IS BG (not weaker).  Since `F_b = (64/621)^{n_b} alpha_b^11 = phi11_rooted(block, root)`
EXACTLY, "`F_b <= 1` for every rooted block" is "`phi11_rooted(T, r) <= 1` for every tree and root", i.e.
`max_r phi11_rooted = bg_phi11 <= 1` -- the Brualdi-Goldwasser conjecture itself.  So the universal bound is
NOT a more-local target; it is the full conjecture, and is NOT proved here.  `conjecture1_proved = False`.

WHERE THE INDUCTION CLOSES, AND WHERE IT DOESN'T (the crux, located).  The per-vertex step
`F_{c} <= 1 for all children  =>  F_v <= 1` closes EXACTLY when `a_v` is small enough: because
`(64/621) * (621/64) = 1`, a vertex with `a_v^11 <= 621/64` ("SAFE") gives
    F_v = (64/621) a_v^11 prod F_c  <=  (64/621)(621/64)(1) = 1
unconditionally.  ~68% of vertices are safe.  The other ~32% are "DANGEROUS": `a_v^11 > 621/64`
(`a_v` up to `15/8`, sup 2), where dropping `prod F_c <= 1` overshoots and the CHILDREN'S SLACK
(`prod F_c < 1`) must compensate.  Dangerous vertices are UNAVOIDABLE: a leaf emits the maximal message
`mu = 1`, so every vertex with a leaf child has `a_v >= 3/2 > rho_B = (621/64)^(1/11) ~ 1.229`, hence every
tree on >= 2 vertices has one.  The compensation is exactly the non-local ANTI-CORRELATION "high-message
children (leaves, `mu = 1`) carry tiny `F = 64/621`" -- PROOF_STATUS dead-end #1 (collective cancellation)
in exact recursive form.  The tie's own hub is the marginal exemplar: `a = 23/18` is DANGEROUS
(`(23/18)^11 > 621/64`) yet `F = 1`, the child slack compensating EXACTLY.

HONEST SCOPE.  The recursion (multi-level lift) is complete and verified.  The universal bound equals BG and
is open; the induction is closed on the safe majority and reduced, on the dangerous minority, to the
collective-cancellation coupling -- a precise localization of the crux, not a proof.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

W = Fr(64, 621)
SAFE_THRESHOLD = Fr(621, 64)   # a_v^11 <= 621/64  <=>  (64/621) a_v^11 <= 1  (rho_B^11, exact-rational)


def _transfer(n, edges, root):
    """Bottom-up transfer.  Returns (F_root, [(vertex_amplitude a_v, message mu_v, factor F_v), ...])."""
    g = {i: set() for i in range(n)}
    for a, b in edges:
        g[a].add(b)
        g[b].add(a)
    table = []

    def rec(v, parent):
        kids = [w for w in g[v] if w != parent]
        sub = [rec(w, v) for w in kids]              # each (F_c, mu_c)
        j = len(kids)
        S = sum((mu for _, mu in sub), Fr(0))
        a = 1 + S * Fr(1, j + 1)
        F = W * a ** 11
        for Fc, _ in sub:
            F *= Fc
        mu = Fr(1) / (j + 1 + S)             # = z/a = 1/((j+1) a) = 1/(j+1+S)
        table.append((a, mu, F))
        return F, mu

    F_root, _ = rec(root, None)
    return F_root, table


def transfer_factor(n, edges, root) -> Fr:
    """The recursive transfer factor `F_root = (64/621)^n (prod a_v)^11 = phi11_rooted(T, root)`."""
    return _transfer(n, edges, root)[0]


def vertex_amplitudes(n, edges, root):
    """The amplitude `a_v` at every vertex under this rooting."""
    return [a for a, _mu, _F in _transfer(n, edges, root)[1]]


def is_safe_vertex(a: Fr) -> bool:
    """A vertex is SAFE if `a^11 <= 621/64` -- then `F_child <= 1 (all children) => F_v <= 1` unconditionally
    (since `(64/621)(621/64) = 1`).  Otherwise DANGEROUS: child slack must compensate."""
    return a ** 11 <= SAFE_THRESHOLD


@dataclass(frozen=True)
class RecursiveTransferCertificate:
    """Lifts the transfer factor to whole trees and reports on the universal bound.  `check()` certifies the
    recursion equals `phi11_rooted` (multi-level lift), the equivalence `universal F<=1  <=>  BG`, the safe/
    dangerous dichotomy with its exact threshold, and the tie hub as the marginal exemplar -- NOT BG."""

    m_max: int = 8

    def recursion_equals_phi(self) -> bool:
        """The per-vertex transfer recursion reproduces `phi11_rooted` for every tree/root up to m_max --
        the multi-level (blocks-of-blocks) lift composes exactly."""
        import networkx as nx
        from .rooted_phi import phi11_rooted
        for m in range(1, self.m_max + 1):
            trees = [nx.empty_graph(1)] if m == 1 else list(nx.nonisomorphic_trees(m))
            for T in trees:
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                for r in range(m):
                    if transfer_factor(m, e, r) != phi11_rooted(m, e, r):
                        return False
        return True

    def universal_bound_is_bg(self) -> bool:
        """The equivalence: the transfer factors of a tree's rootings are exactly its `phi11_rooted` values,
        so `max_r F(T, r) = bg_phi11(T)`.  Hence "`F_b <= 1` for every rooted block" is exactly BG."""
        import networkx as nx
        from .rooted_phi import bg_phi11_fast
        for m in range(2, self.m_max + 1):
            for T in nx.nonisomorphic_trees(m):
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                if max(transfer_factor(m, e, r) for r in range(m)) != bg_phi11_fast(m, e):
                    return False
        return True

    def safe_step_closes(self) -> bool:
        """The exact hook: `(64/621)(621/64) = 1`, so a SAFE vertex (`a^11 <= 621/64`) with all children
        `<= 1` has `F_v <= 1`.  Verified: every vertex whose amplitude is safe AND whose children factors are
        <= 1 indeed has `F_v <= 1` (a self-consistency check of the closing step over the census)."""
        import networkx as nx
        if W * SAFE_THRESHOLD != 1:
            return False
        for m in range(2, self.m_max + 1):
            for T in nx.nonisomorphic_trees(m):
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                for r in range(m):
                    _F, table = _transfer(m, e, r)
                    for a, _mu, F in table:
                        if is_safe_vertex(a) and F > 1:      # a safe vertex must have F <= 1
                            return False
        return True

    def dangerous_vertices_unavoidable(self) -> bool:
        """Every tree on >= 2 vertices has a DANGEROUS vertex (`a^11 > 621/64`): a leaf emits `mu = 1`, so
        its parent has `a >= 3/2`, and `(3/2)^11 > 621/64`.  Verified over the census."""
        import networkx as nx
        if not Fr(3, 2) ** 11 > SAFE_THRESHOLD:
            return False
        for m in range(2, self.m_max + 1):
            for T in nx.nonisomorphic_trees(m):
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                for r in range(m):
                    amps = vertex_amplitudes(m, e, r)
                    if not any(not is_safe_vertex(a) for a in amps):
                        return False
        return True

    def tie_hub_is_dangerous_but_unit(self) -> bool:
        """The tie's hub is the marginal exemplar: `a = 23/18` is DANGEROUS (`(23/18)^11 > 621/64`) yet its
        transfer factor is exactly `F = 1` -- the child slack compensating exactly."""
        from .frustration_free import near_star_edges
        n, e = near_star_edges(5)
        F, table = _transfer(n, e, 0)
        a_hub, _mu, F_hub = table[-1]         # root (hub) is appended last
        return a_hub == Fr(23, 18) and not is_safe_vertex(a_hub) and F_hub == 1 and F == 1

    def safe_fraction(self):
        """(safe, total) vertex counts over the census -- the majority are safe; the crux is the rest."""
        import networkx as nx
        safe = total = 0
        for m in range(2, self.m_max + 1):
            for T in nx.nonisomorphic_trees(m):
                idx = {v: i for i, v in enumerate(T.nodes())}
                e = tuple((idx[a], idx[b]) for a, b in T.edges())
                for r in range(m):
                    for a in vertex_amplitudes(m, e, r):
                        total += 1
                        if is_safe_vertex(a):
                            safe += 1
        return safe, total

    def finding(self) -> str:
        safe, total = self.safe_fraction()
        pct = round(100 * safe / total)
        return (
            "STRUCTURAL LIFT + HONEST NON-CLOSURE. The transfer factor lifts to whole trees: F_v = "
            "(64/621) a_v^11 prod_c F_c with a_v = 1 + S/(j+1), mu_v = 1/(j+1+S) -- verified == phi11_rooted "
            "on all trees (the multi-level blocks-of-blocks lift composes exactly). BUT universal F_b <= 1 IS "
            "BG: F_b = phi11_rooted(block,root), so it equals max_r phi11_rooted <= 1, the full conjecture -- "
            "NOT proved. The induction closes at SAFE vertices (a^11 <= 621/64, since (64/621)(621/64)=1): "
            f"~{pct}% of vertices. The ~{100-pct}% DANGEROUS ones (a up to 15/8) need child slack -- and "
            "dangerous vertices are unavoidable (a leaf emits mu=1 -> parent a >= 3/2). The compensation is "
            "the non-local anti-correlation 'leaf children carry tiny F=64/621' = dead-end #1 in recursive "
            "form; the tie's own hub (a=23/18, dangerous) sits at F=1 by exact slack. Crux LOCATED, not "
            "closed. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the multi-level lift, the equivalence to BG, the safe/dangerous dichotomy with its
        exact threshold, and the tie-hub exemplar -- NOT BG."""
        return (
            self.recursion_equals_phi()
            and self.universal_bound_is_bg()
            and self.safe_step_closes()
            and self.dangerous_vertices_unavoidable()
            and self.tie_hub_is_dangerous_but_unit()
        )

    def lean(self) -> str:
        return (
            "-- RECURSIVE TRANSFER: F_v = (64/621) a_v^11 prod_c F_c, a_v = 1 + S/(j+1), mu_v = 1/(j+1+S).\n"
            "-- Universal F_b <= 1 IS BG (F_b = phi11_rooted).  Safe step: (64/621)(621/64) = 1, so a^11 <=\n"
            "-- 621/64 with children <= 1 gives F_v <= 1.  Dangerous vertices (a^11 > 621/64) are unavoidable.\n"
            "theorem safe_step_scale : (64:ℚ)/621 * (621/64) = 1 := by norm_num\n"
            "theorem leaf_parent_dangerous : ((3:ℚ)/2)^11 > 621/64 := by norm_num\n"
        )
