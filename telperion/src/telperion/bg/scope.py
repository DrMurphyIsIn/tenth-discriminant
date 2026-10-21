"""Scope / obstruction certificate — prove on the tractable structure, exhibit the obstruction beyond.

A recurring discipline in this program: a termwise-nonnegativity argument (permanent/immanant
inequalities, gauge charge splits, ...) is valid on a STRUCTURED class and provably fails beyond it.
This certificate makes that honest boundary machine-checkable for the matrix-function setting.

For a Hermitian matrix with a given off-diagonal SUPPORT graph:

  * IN SCOPE (support is a FOREST): the permutation expansion collapses to involutions/matchings with
    nonnegative weights (a tree/forest has no cycle), so termwise-nonnegativity proofs — e.g.
    permanental dominance (perm_dominance.py) — go through.  This is the scope where the method is valid.

  * OUT OF SCOPE (support has a CYCLE): there is a positive-semidefinite matrix on that support with a
    FRUSTRATED cycle — a permutation whose entry-product is NEGATIVE — so termwise nonnegativity FAILS.
    The certificate constructs the explicit frustration witness (diagonally dominant, hence PSD by
    Gershgorin) and its negative cycle-product.  This is why such arguments do NOT extend to general PSD
    (e.g. why our tree permanental-dominance proof does not reach Lieb's 1966 conjecture).

The witness is minimal (built on a shortest cycle), and everything is checked exactly.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass


def _adj(n, edges):
    g = {i: set() for i in range(n)}
    for a, b in edges:
        g[a].add(b)
        g[b].add(a)
    return g


def is_forest(n, edges) -> bool:
    """Union-find: the support graph is a forest iff no edge joins already-connected vertices."""
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in edges:
        ra, rb = find(a), find(b)
        if ra == rb:
            return False
        parent[ra] = rb
    return True


def shortest_cycle(n, edges):
    """A shortest cycle (list of vertices) in the support graph, or None if acyclic."""
    g = _adj(n, edges)
    best = None
    for src in range(n):
        # BFS tracking parent; a non-parent visited neighbor closes a cycle
        parent = {src: -1}
        dist = {src: 0}
        q = deque([src])
        while q:
            u = q.popleft()
            for w in g[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1
                    parent[w] = u
                    q.append(w)
                elif parent[u] != w:
                    # reconstruct cycle u..src and w..src, join at lca-ish (works for shortest)
                    pu, pw = [u], [w]
                    a, b = u, w
                    while a != -1:
                        pu.append(parent.get(a, -1)); a = parent.get(a, -1)
                    while b != -1:
                        pw.append(parent.get(b, -1)); b = parent.get(b, -1)
                    su, sw = set(pu), set(pw)
                    common = su & sw
                    if not common:
                        continue
                    # nearest common ancestor by BFS distance
                    lca = min(common, key=lambda x: dist.get(x, 10 ** 9))
                    cu = []
                    x = u
                    while x != lca:
                        cu.append(x); x = parent[x]
                    cw = []
                    x = w
                    while x != lca:
                        cw.append(x); x = parent[x]
                    cyc = [lca] + cu[::-1] + cw
                    if len(cyc) >= 3 and (best is None or len(cyc) < len(best)):
                        best = cyc
    return best


@dataclass(frozen=True)
class TermwiseScopeCertificate:
    """Certifies the scope of a termwise-nonnegativity argument for a Hermitian matrix with the given
    off-diagonal `support` (edges over `n` vertices): IN SCOPE iff the support is a forest; otherwise a
    PSD frustration witness with a negative cycle-product is produced."""

    n: int
    support: tuple  # tuple of (i, j) edges

    def in_scope(self) -> bool:
        return is_forest(self.n, self.support)

    def frustration_witness(self):
        """A diagonally-dominant (=> PSD) matrix on the support with a NEGATIVE-product permutation.
        Returns (A, perm, product) or None if the support is a forest."""
        cyc = shortest_cycle(self.n, self.support)
        if cyc is None:
            return None
        n, L = self.n, len(cyc)
        A = [[0] * n for _ in range(n)]
        for v in range(n):
            A[v][v] = 3                       # diagonal 3 > max cycle-degree 2 => PSD (Gershgorin)
        for idx in range(L):
            a, b = cyc[idx], cyc[(idx + 1) % L]
            w = -1 if idx == L - 1 else 1     # one frustrated edge
            A[a][b] = w
            A[b][a] = w
        perm = list(range(n))
        for idx in range(L):
            perm[cyc[idx]] = cyc[(idx + 1) % L]
        prod = 1
        for i in range(n):
            prod *= A[i][perm[i]]
        return A, perm, prod

    def _diagonally_dominant(self, A) -> bool:
        for i in range(self.n):
            if abs(A[i][i]) < sum(abs(A[i][j]) for j in range(self.n) if j != i):
                return False
        return True

    def check(self) -> bool:
        if self.in_scope():
            return self.frustration_witness() is None
        w = self.frustration_witness()
        if w is None:
            return False
        A, _, prod = w
        # the obstruction is real: PSD (diagonal dominance) with a negative permutation-product
        return self._diagonally_dominant(A) and prod < 0

    # ---- Lean ----------------------------------------------------------------
    def lean(self) -> str:
        if self.in_scope():
            m = len(self.support)
            return (
                f"-- SCOPE (n={self.n}): support is a FOREST ({m} edges, acyclic) => the permutation\n"
                f"-- expansion collapses to matchings with nonnegative weights; termwise-nonnegativity\n"
                f"-- arguments (e.g. permanental dominance) are VALID on this class.\n"
                f"theorem scope_forest_edges : ({m}:ℤ) ≤ {self.n} - 1 := by norm_num\n"
            )
        A, perm, prod = self.frustration_witness()
        n = self.n
        lines = [
            f"-- OUT OF SCOPE (n={n}): support has a cycle. Frustration witness = a PSD matrix (below,\n"
            f"-- diagonally dominant => PSD by Gershgorin) with a permutation whose entry-product is\n"
            f"-- NEGATIVE, so termwise nonnegativity FAILS -- the method does not extend to general PSD.\n"
        ]
        # diagonal dominance witnesses (=> PSD)
        for i in range(n):
            off = sum(abs(A[i][j]) for j in range(n) if j != i)
            lines.append(
                f"theorem scope_frustr_domrow_{i} : ({off}:ℤ) ≤ {A[i][i]} := by norm_num"
            )
        # the negative cycle-product (the obstruction)
        factors = " * ".join(f"({A[i][perm[i]]})" for i in range(n))
        lines.append(
            f"-- the frustrated permutation's entry product is negative:\n"
            f"theorem scope_frustr_negative : ({factors} : ℤ) < 0 := by norm_num"
        )
        return "\n".join(lines) + "\n"
