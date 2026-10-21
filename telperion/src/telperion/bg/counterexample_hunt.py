"""Adversarial counterexample hunt -- a quality-diversity search pointed at the open BG pieces.

Refutation is the one mode where evolutionary search is epistemically clean: a FOUND witness is
definitive (it refutes), and an empty hunt is strong evidence.  This uses MAP-Elites
illumination (keep the best fitness per BEHAVIOR niche, not just the global best) so the search explores
strange tree shapes instead of collapsing back onto the near-star -- a counterexample, if it exists, hides
in an unusual structure far from the known peak, exactly where niche-diversity search looks.

Two hunts, both over GENERAL trees (beyond the spider subclass rectification.py proves, and beyond the
exhaustive census range):

  hunt_dominance(n): maximize density D=Phi^11^(1/n).  A niche reaching the legs-2 reference REFUTES
      legs-2 dominance; any D >= 1 at n != 11 REFUTES Brualdi-Goldwasser itself.

  probe_monotonicity(n): sample legs-2-directed leaf relocations (moves that reduce total |arm-2|) on
      general trees and report how often / how badly they DECREASE Phi -- stress-testing whether the
      spider per-move basis extends to general trees.

Pure Python by design (the search is untrusted; only exact Phi matters).  This is a RESEARCH SCAFFOLD:
it can REFUTE (a witness) but never PROVE.  conjecture1_proved = False.
"""
from __future__ import annotations

from dataclasses import dataclass, field

try:
    import networkx as nx
    _NX = True
except Exception:  # pragma: no cover
    _NX = False

from .fractal_eigenvalue import near_star_edges
from .rooted_phi import bg_phi11_fast


def _edges_of(T):
    idx = {v: i for i, v in enumerate(T.nodes())}
    return T.number_of_nodes(), tuple((idx[a], idx[b]) for a, b in T.edges())


def _density(T):
    n, e = _edges_of(T)
    return float(bg_phi11_fast(n, e)) ** (1.0 / n)


def _behavior(T):
    """Niche descriptor: (max degree, #leaves, diameter) -- coarse tree-shape coordinates."""
    degs = [d for _, d in T.degree()]
    leaves = sum(1 for d in degs if d == 1)
    return (max(degs), leaves, nx.diameter(T))


def _legs2_reference(n):
    """The legs-2 density to beat at order n: near-star for odd n; None if no pure legs-2 tree exists."""
    if n % 2 == 1:
        nn, e = near_star_edges((n - 1) // 2)
        return float(bg_phi11_fast(nn, e)) ** (1.0 / nn)
    if n % 4 == 2:                                   # double-broom exists
        a = (n - 2) // 4
        e = [(0, 1)]; nid = 2
        for h in (0, 1):
            for _ in range(a):
                e += [(h, nid), (nid, nid + 1)]; nid += 2
        return float(bg_phi11_fast(n, e)) ** (1.0 / n)
    return None                                      # n % 4 == 0: parity gap, no pure legs-2


def _mutate(T, rng):
    """n-preserving move: detach a random leaf, reattach elsewhere (keeps it a tree)."""
    T2 = T.copy()
    leaves = [v for v in T2 if T2.degree(v) == 1]
    lf = rng.choice(leaves)
    nb = next(iter(T2[lf]))
    cand = [v for v in T2 if v != lf and v != nb]
    if not cand:
        return None
    T2.remove_edge(lf, nb)
    T2.add_edge(lf, rng.choice(cand))
    return T2 if nx.is_tree(T2) else None


@dataclass
class CounterexampleHunt:
    """MAP-Elites illumination over general trees on n vertices, hunting a density that beats legs-2."""

    n: int
    seed: int = 0
    pop: int = 40
    gens: int = 60
    archive: dict = field(default_factory=dict)   # behavior cell -> (D, tree)

    def _place(self, T):
        D = _density(T)
        b = _behavior(T)
        cur = self.archive.get(b)
        if cur is None or D > cur[0]:
            self.archive[b] = (D, T)

    def hunt(self):
        import random
        rng = random.Random(self.seed)
        for _ in range(self.pop):
            self._place(nx.random_labeled_tree(self.n, seed=rng.randint(0, 2**31)))
        for _ in range(self.gens):
            elites = list(self.archive.values())
            for _D, T in elites:
                for _ in range(2):
                    T2 = _mutate(T, rng)
                    if T2 is not None:
                        self._place(T2)
        bestD, bestT = max(self.archive.values(), key=lambda x: x[0])
        ref = _legs2_reference(self.n)
        return {
            "n": self.n,
            "best_D": bestD,
            "legs2_ref": ref,
            "beats_ref": (ref is not None and bestD > ref + 1e-12),
            "refutes_bg": bestD >= 1.0 - 1e-12 and self.n != 11,
            "niches": len(self.archive),
            "best_degseq": sorted((d for _, d in bestT.degree()), reverse=True),
        }


def near_star_seeds(n, count=40, kicks=3, seed=0):
    """Bonsai seed set: the near-star ideal form plus `count` cultivated perturbations (each a few
    prune-regraft 'kicks' away).  Seeds the hunt AT the peak so islands must climb ABOVE it to refute."""
    import random
    from .parallel_map import _prune_regraft
    rng = random.Random(seed)
    if n % 2 == 1:
        _, base = near_star_edges((n - 1) // 2)
    else:                                            # even n: near-star with one length-1 stub
        _, ns = near_star_edges((n - 2) // 2)
        base = ns + ((0, n - 1),)
    out = [base]
    for _ in range(count):
        e = base
        for _ in range(rng.randint(1, kicks)):
            e2 = _prune_regraft(n, e, rng.randint(0, 999), rng.randint(0, 999))
            if e2 is not None:
                e = e2
        out.append(e)
    return out


def scaled_hunt(n, n_islands=8, epochs=6, rounds=60, seed=0, workers=None):
    """Scaled bonsai hunt: IslandModel (parallel MAP-Elites, migration) SEEDED at the near-star, hunting
    for any tree whose rooted Phi^11 exceeds the near-star's.  A hit REFUTES (>near-star at n!=11, or >=1).
    Returns the best found vs the near-star reference -- honest about whether the engine even held the peak.

    NOTE: uses multiprocessing (spawn), so call it from a `if __name__ == '__main__':` guarded script,
    not an interactive/stdin session (the workers must be able to re-import the driver module)."""
    from .parallel_map import IslandModel
    seeds = near_star_seeds(n, count=max(20, n_islands * 4), seed=seed)
    arch = IslandModel(n=n, n_islands=n_islands).run(
        epochs=epochs, rounds_per_epoch=rounds, migrants=n_islands * 2,
        workers=workers, initial_seeds=seeds)
    best_phi, best_e = max(arch.values(), key=lambda x: x[0])
    ref_phi = bg_phi11_fast(*_ns_ref(n))
    from collections import Counter
    deg = Counter()
    for a, b in best_e:
        deg[a] += 1; deg[b] += 1
    return {
        "n": n,
        "best_phi11": float(best_phi),
        "near_star_phi11": float(ref_phi),
        "held_peak": bool(best_phi >= ref_phi - 1e-12),
        "beats_near_star": bool(best_phi > ref_phi + 1e-9),
        "refutes_bg": bool(best_phi >= 1.0 - 1e-9 and n != 11),
        "niches": len(arch),
        "best_degseq": sorted(deg.values(), reverse=True),
    }


def _ns_ref(n):
    if n % 2 == 1:
        return near_star_edges((n - 1) // 2)
    _, ns = near_star_edges((n - 2) // 2)
    return n, ns + ((0, n - 1),)


def probe_monotonicity(n, samples=2000, seed=0):
    """Over random general trees, sample legs-2-directed leaf relocations (reduce total |arm-2|) and
    report how often they DECREASE Phi -- does the spider per-move basis extend to general trees?"""
    import random
    rng = random.Random(seed)

    def leg_dev(T):
        hubs = [v for v in T if T.degree(v) >= 3]
        if not hubs:
            return 0
        return sum(abs(min(nx.shortest_path_length(T, lf, h) for h in hubs) - 2)
                   for lf in T if T.degree(lf) == 1)

    tested = decreases = 0
    worst = 0.0
    for _ in range(samples):
        T = nx.random_labeled_tree(n, seed=rng.randint(0, 2**31))
        d0 = leg_dev(T)
        if d0 == 0:
            continue
        T2 = _mutate(T, rng)
        if T2 is None or leg_dev(T2) >= d0:          # must move TOWARD legs-2
            continue
        tested += 1
        delta = _density(T2) - _density(T)
        if delta < -1e-12:
            decreases += 1
            worst = min(worst, delta)
    return {"n": n, "tested": tested, "decreases": decreases,
            "frac": (decreases / tested if tested else None), "worst_delta": worst}
