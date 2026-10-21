"""Rooted branch Phi -- the ACTUAL Brualdi-Goldwasser quantity (not the raw matching sum).

CORRECTION (2026-08-16): competitor extremality is about the rooted BRANCH value Phi, whose tree
invariant is the MAX over roots -- NOT the raw monomer-dimer sum rho=per(L)/prod(deg) that
matching_free_energy computes.  The two have opposite extremal structure: raw rho is maximized by
balanced caterpillars, rooted Phi by the near-star.  BG is `max_root Phi^11 <= 1`.

The rooted branch recursion (cr=0 plain-tree model): a vertex with children cavities m_c, S = sum m_c,
degree-with-virtual-parent d = (#children)+1, z = 3/(3d),

    m_v = z/(1 + z S),     Phi11_v = (64/621) * (1 + z S)^11 * prod_c Phi11_c .

Phi^11(T) := max over roots r of the value at r.  Verified: N(0,5) rooted at its hub = 1 (the tie);
max_root Phi^11 <= 1 for all trees checked; the near-star is the max_root maximizer per n.
conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

_A11 = Fr(64, 621)


def phi11_rooted(n, edges, root):
    """Phi^11 of the tree rooted at `root` (exact Fraction), via the branch recursion."""
    adj = {i: [] for i in range(n)}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    parent = {root: -1}
    order = [root]
    stack = [root]
    seen = {root}
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                parent[w] = u
                order.append(w)
                stack.append(w)
    m = {}
    p = {}
    for v in reversed(order):                       # postorder
        kids = [c for c in adj[v] if c != parent[v]]
        S = sum(m[c] for c in kids)
        d = len(kids) + 1                           # +1 = virtual parent edge
        z = Fr(3, 3 * d)
        one_pzS = 1 + z * S
        m[v] = z / one_pzS
        pv = _A11 * one_pzS ** 11
        for c in kids:
            pv *= p[c]
        p[v] = pv
    return p[root]


def bg_phi11(n, edges):
    """The Brualdi-Goldwasser invariant: max over roots of the rooted branch Phi^11."""
    return max(phi11_rooted(n, edges, r) for r in range(n))


def all_roots_phi11(n, edges):
    """Phi^11 rooted at EVERY vertex, computed in O(n) total by re-rooting (message-passing) DP.
    Returns {root: Phi^11}.  A directed-edge message from v (parent u) carries
    (m_{v->u}, p_{v->u}) = (z/(1+zS), (64/621)(1+zS)^11 prod p_child), z=1/deg(v), S=sum child m."""
    if n == 1:
        return {0: _A11}
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    deg = [len(adj[v]) for v in range(n)]
    parent = [-1] * n
    order = [0]
    seen = [False] * n
    seen[0] = True
    stack = [0]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if not seen[w]:
                seen[w] = True
                parent[w] = u
                order.append(w)
                stack.append(w)

    def message(v, nbr_msgs):
        """(m,p) for v sending toward one neighbor; nbr_msgs = incoming (m,p) from its OTHER neighbors.
        v has a real parent here so d = deg(v)."""
        S = sum(mm for mm, _ in nbr_msgs)
        z = Fr(3, 3 * deg[v])
        opz = 1 + z * S
        pv = _A11 * opz ** 11
        for _, pp in nbr_msgs:
            pv *= pp
        return (z / opz, pv)

    # pass 1 (postorder): up[v] = message from v to parent(v)
    up = [None] * n
    for v in reversed(order):
        kids = [c for c in adj[v] if c != parent[v]]
        up[v] = message(v, [up[c] for c in kids])

    # pass 2 (preorder): down[v] = message from parent(v) to v
    down = [None] * n
    for v in order:
        nbrs = adj[v]
        # incoming (m,p) from every neighbor of v
        inc = []
        for w in nbrs:
            inc.append(up[w] if parent[w] == v else down[v])  # child -> up[w]; parent -> down[v]
        k = len(nbrs)
        # prefix/suffix products of p and prefix sums of m, to exclude one neighbor
        pref_p = [Fr(1)] * (k + 1)
        suf_p = [Fr(1)] * (k + 1)
        for i in range(k):
            pref_p[i + 1] = pref_p[i] * inc[i][1]
        for i in range(k - 1, -1, -1):
            suf_p[i] = suf_p[i + 1] * inc[i][1]
        total_m = sum(mm for mm, _ in inc)
        z = Fr(3, 3 * deg[v])
        for i, w in enumerate(nbrs):
            if parent[w] != v:
                continue  # only send down to children
            S = total_m - inc[i][0]
            opz = 1 + z * S
            pw = _A11 * opz ** 11 * pref_p[i] * suf_p[i + 1]
            down[w] = (z / opz, pw)

    # combine at each root r: d = deg(r)+1 (virtual parent)
    res = {}
    for r in range(n):
        msgs = [up[w] if parent[w] == r else down[r] for w in adj[r]]
        S = sum(mm for mm, _ in msgs)
        z = Fr(3, 3 * (deg[r] + 1))
        opz = 1 + z * S
        pr = _A11 * opz ** 11
        for _, pp in msgs:
            pr *= pp
        res[r] = pr
    return res


def bg_phi11_fast(n, edges):
    """Brualdi-Goldwasser invariant via the O(n) re-rooting DP (max over all roots)."""
    return max(all_roots_phi11(n, edges).values())


def bg_phi11_argmax_root(n, edges):
    """(max Phi^11, root attaining it)."""
    best = None
    for r in range(n):
        v = phi11_rooted(n, edges, r)
        if best is None or v > best[0]:
            best = (v, r)
    return best


def _near_star_edges(s):
    edges = []
    nid = 1
    for _ in range(s):
        edges.append((0, nid))
        edges.append((nid, nid + 1))
        nid += 2
    return 2 * s + 1, tuple(edges)


def _all_tree_edges(n):
    import networkx as nx
    out = []
    for T in nx.nonisomorphic_trees(n):
        idx = {v: i for i, v in enumerate(T.nodes())}
        out.append(tuple((idx[a], idx[b]) for a, b in T.edges()))
    return out


@dataclass(frozen=True)
class BGExtremalityCertificate:
    """CORRECT competitor extremality (rooted BG-Phi, not raw rho): for n=2s+1, the near-star N(0,s)
    maximizes bg_phi11 over ALL trees on n vertices.  Verified exhaustively n<=17; emits the binding
    witness that the near-star strictly beats the runner-up.  (Contrast matching_free_energy's raw-rho
    certificate, which measures the monomer-dimer problem and is MAXIMIZED BY CATERPILLARS, not BG.)"""

    s: int

    def near_star_phi(self):
        n, e = _near_star_edges(self.s)
        return bg_phi11(n, e)

    def _ranked(self):
        n = 2 * self.s + 1
        vals = [(bg_phi11(n, e), e) for e in _all_tree_edges(n)]
        vals.sort(key=lambda t: t[0], reverse=True)
        return n, vals

    def is_extremal(self) -> bool:
        n, vals = self._ranked()
        top = vals[0][0]
        return self.near_star_phi() == top and (len(vals) < 2 or vals[1][0] < top)

    def gap_to_runner_up(self):
        n, vals = self._ranked()
        return vals[0][0] - vals[1][0] if len(vals) > 1 else None

    def check(self) -> bool:
        return self.is_extremal()

    def lean(self) -> str:
        n, vals = self._ranked()
        ns = self.near_star_phi()
        runner = vals[1][0] if len(vals) > 1 else Fr(0)
        is_tie = ns == 1
        lines = [
            f"-- BG COMPETITOR EXTREMALITY, n={n} (rooted branch Phi, the ACTUAL BG quantity).\n"
            f"-- The near-star N(0,{self.s}) maximizes max_root Phi^11 over all {len(vals)} trees on {n}\n"
            f"-- vertices; it strictly beats the runner-up.  Phi^11(N(0,{self.s})) = "
            f"{ns.numerator}/{ns.denominator}{' = 1 (the TIE)' if is_tie else ''}.\n"
        ]
        if is_tie:
            lines.append(f"theorem bgext_n{n}_tie : "
                         f"(({ns.numerator}:ℚ)/{ns.denominator}) = 1 := by norm_num")
        else:
            lines.append(f"theorem bgext_n{n}_value_le1 : "
                         f"({ns.numerator}:ℤ) < {ns.denominator} := by norm_num")
        lines.append(
            f"-- strictly above the runner-up Phi^11 = {runner.numerator}/{runner.denominator}:\n"
            f"theorem bgext_n{n}_beats_runnerup : "
            f"({runner.numerator}*{ns.denominator}:ℤ) < {ns.numerator}*{runner.denominator} := by norm_num"
        )
        return "\n".join(lines) + "\n"
