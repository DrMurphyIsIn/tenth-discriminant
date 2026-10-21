"""Recursive transfer factor (the multi-level lift) tests.

Pins: the per-vertex recursion reproduces phi11_rooted on all trees (the blocks-of-blocks lift); the
universal bound F_b <= 1 equals BG (max_r F = bg_phi11); the safe/dangerous dichotomy with its exact
rational threshold; and the tie hub as the marginal exemplar. BG is NOT proved -- the universal bound
IS the conjecture. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest

nx = pytest.importorskip("networkx")  # graph certificates need networkx; skip cleanly if absent

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    RecursiveTransferCertificate,
    is_safe_vertex,
    transfer_factor,
    vertex_amplitudes,
)
from telperion.bg.frustration_free import near_star_edges  # noqa: E402
from telperion.bg.rooted_phi import bg_phi11_fast, phi11_rooted  # noqa: E402


def _edges(T):
    idx = {v: i for i, v in enumerate(T.nodes())}
    return tuple((idx[a], idx[b]) for a, b in T.edges())


def test_recursion_equals_phi11_rooted_multilevel():
    # the per-vertex transfer recursion reproduces phi11_rooted on every tree/root (the lift composes)
    for m in range(1, 8):
        trees = [nx.empty_graph(1)] if m == 1 else list(nx.nonisomorphic_trees(m))
        for T in trees:
            e = _edges(T)
            for r in range(m):
                assert transfer_factor(m, e, r) == phi11_rooted(m, e, r)


def test_universal_bound_equals_bg():
    # max over rootings of the transfer factor == bg_phi11 -> "F_b <= 1 for all blocks" IS BG
    for m in range(2, 8):
        for T in nx.nonisomorphic_trees(m):
            e = _edges(T)
            assert max(transfer_factor(m, e, r) for r in range(m)) == bg_phi11_fast(m, e)


def test_safe_threshold_is_exact_and_closes_the_step():
    # (64/621)*(621/64) = 1, so a^11 <= 621/64 with children <= 1 gives F_v <= 1
    assert Fr(64, 621) * Fr(621, 64) == 1
    assert is_safe_vertex(Fr(1))                       # a leaf (a=1) is safe
    assert is_safe_vertex(Fr(6, 5))                    # (6/5)^11 < 621/64
    assert not is_safe_vertex(Fr(3, 2))                # (3/2)^11 > 621/64  -> dangerous


def test_dangerous_vertices_unavoidable():
    # every tree on >= 2 vertices has a vertex with a leaf child (a >= 3/2), hence a dangerous vertex
    assert Fr(3, 2) ** 11 > Fr(621, 64)
    for m in range(2, 8):
        for T in nx.nonisomorphic_trees(m):
            e = _edges(T)
            for r in range(m):
                assert any(not is_safe_vertex(a) for a in vertex_amplitudes(m, e, r))


def test_tie_hub_is_dangerous_but_unit():
    # the tie's hub: a = 23/18 is dangerous yet F = 1 (child slack compensates exactly)
    n, e = near_star_edges(5)
    assert not is_safe_vertex(Fr(23, 18))
    assert transfer_factor(n, e, 0) == 1
    amps = vertex_amplitudes(n, e, 0)
    assert Fr(23, 18) in amps


def test_certificate_check_and_scope():
    cert = RecursiveTransferCertificate(m_max=7)
    assert cert.check()
    safe, total = cert.safe_fraction()
    assert 0 < safe < total                            # a majority safe, a real dangerous minority
    f = cert.finding()
    assert "IS BG" in f and "conjecture1_proved = False" in f
