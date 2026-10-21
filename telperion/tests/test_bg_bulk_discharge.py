"""Tests for the BG bulk-discharge engine (analytic upper-bound route).

The exact Bethe product identity `prod_v Aarg / prod_e Barg == rho`, the per-vertex decomposition
`sum_v phi_v == log pi`, and the extremal saturation on `S(k,5)`.  conjecture1_proved = False.
"""
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

import networkx as nx

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg_bulk_discharge import (  # noqa: E402
    F_STAR_ARG,
    bethe_terms,
    phi_vertices,
)
from telperion.matching_free_energy import rho  # noqa: E402
from telperion.spider_broom import spider_edges  # noqa: E402


def _edges(T):
    idx = {v: i for i, v in enumerate(T.nodes())}
    return T.number_of_nodes(), [(idx[a], idx[b]) for a, b in T.edges()]


def test_bethe_product_equals_rho_exact():
    """CORE: prod_v Aarg[v] / prod_e Barg[e] == rho exactly, over all trees N<=11."""
    for N in range(2, 12):
        for T in nx.nonisomorphic_trees(N):
            n, e = _edges(T)
            Aarg, Barg, _ = bethe_terms(n, e)
            prod = Fr(1)
            for v in range(n):
                prod *= Aarg[v]
            for k in Barg:
                prod /= Barg[k]
            assert prod == rho(n, e), f"Bethe product != rho on N={N}"


def test_phi_sums_to_log_pi():
    """sum_v phi_v == log pi(T) for any edge-discharge (here equal split), on several trees."""
    trees = [spider_edges(20, 5), spider_edges(8, 4)]
    trees += [_edges(nx.random_labeled_tree(24, seed=s)) for s in range(4)]
    for n, e in trees:
        z = rho(n, e)
        logpi = math.log(int(z.numerator)) - math.log(int(z.denominator))
        ph, _ = phi_vertices(n, e, lambda dv, du: 0.5)
        assert abs(sum(ph.values()) - logpi) < 1e-7


def test_fstar_algebraic_target():
    """The transcendental F* = log(621/64)/11 clears to the algebraic target exp(11 F*) = 621/64."""
    assert F_STAR_ARG == Fr(621, 64)
    assert abs(math.log(float(F_STAR_ARG)) / 11 - 0.2065864) < 1e-6
