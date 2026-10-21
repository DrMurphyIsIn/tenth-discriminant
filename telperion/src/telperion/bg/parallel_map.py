"""Parallel island model + migration for empirical mapping of the tree landscape.

A standard island model (parallel populations with periodic migration).
Uses Python multiprocessing (ProcessPoolExecutor) for real across-core parallelism -- the practical
acceleration for empirical variable mapping, where the bottleneck is the NUMBER of trees/configs
evaluated (each rho evaluation is already linear-time via the cavity DP).

DESIGN NOTE on Rust / MLX.  Telperion is deliberately PURE PYTHON: the certificate generator is
untrusted by design, the Lean kernel is the sole trusted component, so the audit surface must stay
readable (see the project plan -- "no Rust").  A Rust NEON / MLX GPU kernel would contradict that
principle and belongs in the private research monorepo (a separate native build step), OUTSIDE the
trusted certificate path.  For tree-rho mapping this costs nothing: the per-evaluation work is linear
and the workload is embarrassingly parallel, so PROCESS-level parallelism delivers the scaling (one
core per island / per parameter cell) without a native dependency.  The `evaluator` hook below lets a
faster backend slot in behind the same interface if a genuine hot loop ever appears.

Two tools:
  * IslandModel  -- N MAP-Elites islands exploring the tree landscape in parallel, migrating elites
    between epochs (diverse move-offsets keep islands from collapsing to the same search).
  * parallel_sweep -- embarrassingly-parallel map of a picklable function over a parameter grid, for
    mapping rho-landscape variables (n, leg distributions, hub counts, ...) across all cores at once.
"""
from __future__ import annotations

from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass

from .matching_free_energy import near_star_edges, rho
from .tree_search import TreeLandscapeSearch, _prune_regraft


# ---- island worker (top-level so it is picklable under spawn) ---------------
def _run_island(job):
    """Run one MAP-Elites island for `rounds` with an island-specific move offset (for diversity).
    job = (n, seed_edges, rounds, offset).  Returns (offset, archive)."""
    n, seed_edges, rounds, offset = job
    S = TreeLandscapeSearch(n)
    for e in seed_edges:
        S._consider(e)
    if not S.archive:
        S.seed()
    for r in range(rounds):
        for (_, edges) in list(S.archive.values()):
            for i in range((r % 3) + 1):
                for j in range((r % 4) + 1):
                    e = _prune_regraft(n, edges, i + r + offset, j + r + 2 * offset)
                    if e is not None:
                        S._consider(e)
    return offset, dict(S.archive)


@dataclass
class IslandModel:
    """N parallel MAP-Elites islands over trees on n vertices, migrating elites between epochs."""

    n: int
    n_islands: int = 4

    def run(self, epochs: int = 3, rounds_per_epoch: int = 40, migrants: int = 8, workers=None,
            initial_seeds=None):
        base = list(initial_seeds) if initial_seeds else []
        seeds = [list(base) for _ in range(self.n_islands)]
        global_archive: dict = {}
        for _epoch in range(epochs):
            jobs = [(self.n, tuple(seeds[i]), rounds_per_epoch, i + 1) for i in range(self.n_islands)]
            with ProcessPoolExecutor(max_workers=workers) as ex:
                results = list(ex.map(_run_island, jobs))
            for _off, arch in results:
                for cell, (r, e) in arch.items():
                    if cell not in global_archive or r > global_archive[cell][0]:
                        global_archive[cell] = (r, e)
            # migration: broadcast the current global elites as seeds for the next epoch
            elites = [e for (_c, (_r, e)) in
                      sorted(global_archive.items(), key=lambda kv: kv[1][0], reverse=True)[:migrants]]
            seeds = [list(elites) for _ in range(self.n_islands)]
        return global_archive

    def best(self, archive=None):
        a = archive if archive is not None else self.run()
        return max(a.values(), key=lambda x: x[0])


# ---- generic parallel parameter sweep --------------------------------------
def parallel_sweep(fn, items, workers=None):
    """Map a PICKLABLE top-level function `fn` over `items` across cores; returns the list of results.
    For empirical mapping of rho-landscape variables (one parameter cell per core)."""
    with ProcessPoolExecutor(max_workers=workers) as ex:
        return list(ex.map(fn, items))


# ---- a ready-made sweep cell: max-rho tree for a given odd n ----------------
def max_rho_for_n(n):
    """Parallel-map target: illuminate trees on n vertices, return (n, best_rho, is_near_star)."""
    S = TreeLandscapeSearch(n)
    S.illuminate(rounds=100)
    rbest, _ = S.best()
    if n % 2 == 1:
        ns = rho(n, near_star_edges((n - 1) // 2)[1])
        return (n, rbest, rbest == ns)
    return (n, rbest, None)
