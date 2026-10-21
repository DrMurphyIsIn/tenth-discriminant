"""Frustration-free / parent-Hamiltonian core (Tier-B #3 for Brualdi-Goldwasser) tests.

Pins the constructed facts: the integer-bond-dimension (=2) monomer-dimer MPS reproduces the matching
partition function; the tie is the isolated gapless point; the transfer gap closes along the whole
tie-recursive family (so no uniform Knabe threshold). BG itself is NOT proved -- the <= half is a
frustration-free positivity the Knabe route does not close. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    FrustrationFreeGapProbe,
    monomer_dimer_partition,
    tie_recursive_edges,
    transfer_density,
)
from telperion.bg.frustration_free import near_star_edges  # noqa: E402
from telperion.bg.graphlimit import matching_polynomial  # noqa: E402


def _adj(n, edges):
    a = {i: set() for i in range(n)}
    for u, v in edges:
        a[u].add(v)
        a[v].add(u)
    return a


def test_mps_bond_dim_2_reproduces_matchings():
    # the frustration-free ground-state tensor has integer bond dimension 2, exact partition function
    for s in range(2, 8):
        n, e = near_star_edges(s)
        assert monomer_dimer_partition(n, e) == sum(matching_polynomial(_adj(n, e)))
    assert FrustrationFreeGapProbe().bond_dimension() == 2


def test_weighted_mps_is_matching_generating_polynomial():
    # with a symbolic fugacity x, the MPS transfer yields sum_k m_k x^k exactly
    x = sp.Symbol("x")
    n, e = near_star_edges(3)
    mk = matching_polynomial(_adj(n, e))                 # [1, 6, 9, 4]
    gen = sum(m * x ** k for k, m in enumerate(mk))
    assert sp.expand(monomer_dimer_partition(n, e, x=x) - gen) == 0


def test_mps_on_a_path_matches_fibonacci_matchings():
    # a path P_m has (F_{m+1}) matchings; check the transfer on a small path
    path = (0, ((0, 1), (1, 2), (2, 3), (3, 4)))         # P_5: matchings = 8
    n, e = 5, path[1]
    assert monomer_dimer_partition(n, e) == sum(matching_polynomial(_adj(n, e)))
    assert monomer_dimer_partition(n, e) == 8


def test_tie_is_isolated_gapless_point_on_near_stars():
    probe = FrustrationFreeGapProbe()
    # D = 1 exactly at the tie, D < 1 (gapped) off it
    n5, e5 = near_star_edges(5)
    from telperion.bg.rooted_phi import bg_phi11_fast
    assert bg_phi11_fast(n5, e5) == 1
    for s in (2, 3, 4, 6, 7):
        n, e = near_star_edges(s)
        assert bg_phi11_fast(n, e) < 1
    assert probe.tie_is_gapless()


def test_gap_closes_on_tie_recursive_family():
    # density strictly rises toward 1 (gap -> 0) as k grows, but stays < 1 at every finite k
    ks = (1, 2, 3, 5, 10, 20)
    ds = [transfer_density(*tie_recursive_edges(k)) for k in ks]
    assert all(b > a for a, b in zip(ds, ds[1:]))        # strictly increasing
    assert all(d < 1 for d in ds)                        # gap > 0 at every finite k
    assert ds[-1] > 0.99                                 # demonstrably approaching 1
    assert FrustrationFreeGapProbe().gap_closes_on_tie_recursive_family()


def test_no_uniform_knabe_threshold_and_check():
    probe = FrustrationFreeGapProbe()
    # the gap closes on a whole family -> no uniform local-gap threshold exists
    assert probe.knabe_uniform_threshold_exists() is False
    assert probe.check()
    f = probe.finding()
    assert "OBSTRUCTION" in f and "conjecture1_proved = False" in f
