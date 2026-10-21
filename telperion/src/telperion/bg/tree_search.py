"""Tree-landscape search for competitor extremality — MAP-Elites illumination + rearrangement moves.

Ideas gleaned from a private research evolution engine (read-only review), adapted to the
Brualdi-Goldwasser tree landscape (fitness = bg_phi11(T), the ROOTED branch Phi, max over roots -- the
CORRECT BG quantity, re-pointed 2026-08-16 from the raw monomer-dimer rho which is a different problem):

  * MAP-ELITES illumination (map_elites/archive.py): store the best tree per cell of a structural
    behavior grid (diameter x max-degree).  This illuminates the WHOLE landscape -- confirming the
    near-star is the global peak AND exposing the runner-up niches -- rather than only chasing the max.
  * MEMETIC local search (memetic/local_search.py): rearrangement MOVES (prune-and-regraft = leg-split,
    hub-merge, arm-add) are the local operators; hill-climb by them, testing rho-monotonicity.
  * NOVELTY-driven diversity (open_ended/novelty_tracker.py): fill empty niches to adversarially hunt
    for any tree that beats the near-star (a counterexample search for competitor extremality).

Unlike exhaustive enumeration (infeasible past ~n=16), this explores large-n tree-space and checks the
near-star stays the peak -- extending the competitor-extremality evidence.  It is a SEARCH (evidence),
not a proof.  conjecture1_proved=False.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from .matching_free_energy import near_star_edges
from .rooted_phi import bg_phi11_fast


def _descriptor(n, edges):
    """Structural behavior descriptor of a tree: (diameter, max_degree)."""
    adj = {i: [] for i in range(n)}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    maxdeg = max(len(adj[v]) for v in range(n))

    def bfs_far(s):
        dist = {s: 0}
        q = [s]
        while q:
            u = q.pop(0)
            for w in adj[u]:
                if w not in dist:
                    dist[w] = dist[u] + 1
                    q.append(w)
        far = max(dist, key=lambda x: dist[x])
        return far, dist[far]

    a, _ = bfs_far(0)
    _, diam = bfs_far(a)
    return (diam, maxdeg)


def _prune_regraft(n, edges, i, j):
    """Rearrangement move: detach a leaf and reattach it elsewhere (deterministic by indices i,j).
    Returns new edge tuple, or None if the move is degenerate."""
    adj = {v: [] for v in range(n)}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    leaves = [v for v in range(n) if len(adj[v]) == 1]
    if not leaves:
        return None
    leaf = leaves[i % len(leaves)]
    old = adj[leaf][0]
    cands = [v for v in range(n) if v != leaf and v != old]
    if not cands:
        return None
    new = cands[j % len(cands)]
    e = [(a, b) for (a, b) in edges if {a, b} != {leaf, old}]
    e.append((leaf, new))
    return tuple(e)


@dataclass
class TreeLandscapeSearch:
    """MAP-Elites illumination of the rho landscape over trees on n vertices, with rearrangement-move
    local search.  archive[cell] = (rho, edges) best per (diameter, max_degree) niche."""

    n: int
    archive: dict = field(default_factory=dict)

    def _consider(self, edges):
        r = bg_phi11_fast(self.n, edges)
        cell = _descriptor(self.n, edges)
        if cell not in self.archive or r > self.archive[cell][0]:
            self.archive[cell] = (r, edges)
            return True
        return False

    def seed(self):
        """Seed with the near-star (if n odd) and a path."""
        if self.n % 2 == 1:
            _, e = near_star_edges((self.n - 1) // 2)
            self._consider(e)
        self._consider(tuple((i, i + 1) for i in range(self.n - 1)))  # path

    def illuminate(self, rounds: int = 200):
        """Deterministic MAP-Elites: repeatedly apply rearrangement moves to occupied cells, keeping
        the best per niche.  Deterministic (no RNG) so results are reproducible/certifiable."""
        self.seed()
        for r in range(rounds):
            for (_, edges) in list(self.archive.values()):
                for i in range((r % 3) + 1):
                    for j in range((r % 4) + 1):
                        e = _prune_regraft(self.n, edges, i + r, j + r)
                        if e is not None:
                            self._consider(e)
        return self.archive

    def best(self):
        return max(self.archive.values(), key=lambda x: x[0])

    def near_star_is_peak(self) -> bool:
        """The global max over the illuminated archive is the near-star (odd n)."""
        if self.n % 2 == 0:
            return False
        rho_best, _ = self.best()
        _, nse = near_star_edges((self.n - 1) // 2)
        return rho_best == bg_phi11_fast(self.n, nse)
