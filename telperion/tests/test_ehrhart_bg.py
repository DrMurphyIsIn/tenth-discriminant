"""Ehrhart / lattice-point probe (Tier-B #2 for Brualdi-Goldwasser) tests.

The finding is NEGATIVE by design (the tree matching polytope is integral -> Ehrhart period 1,
never 23); these tests pin the exact lattice-point engine (tree-DP vs brute force) and the
reproducibility of that negative result. conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    EhrhartBGProbe,
    matching_polytope_ehrhart,
    matching_polytope_ehrhart_bruteforce,
)
from telperion.bg.ehrhart import fit_polynomial, is_quasi_polynomial  # noqa: E402
from telperion.bg.matching_free_energy import near_star_edges  # noqa: E402


def test_ehrhart_dp_matches_bruteforce():
    for s in (2, 3, 4):
        n, edges = near_star_edges(s)
        T = 2 * s + 2
        assert matching_polytope_ehrhart(n, edges, T) == matching_polytope_ehrhart_bruteforce(n, edges, T)


def test_ehrhart_known_values():
    n, edges = near_star_edges(2)
    assert matching_polytope_ehrhart(n, edges, 6) == [1, 8, 31, 85, 190, 371, 658]
    n, edges = near_star_edges(3)
    assert matching_polytope_ehrhart(n, edges, 4) == [1, 20, 144, 631, 2058]


def test_matching_polytope_is_integral_period_one():
    # a tree is bipartite -> matching polytope integral -> Ehrhart is a genuine polynomial
    n, edges = near_star_edges(5)          # E = 10, degree-10 Ehrhart polynomial
    seq = matching_polytope_ehrhart(n, edges, 13)
    assert is_quasi_polynomial(seq, 1, max_deg=10)          # genuine polynomial, period 1
    coeffs = fit_polynomial(list(range(len(seq))), seq, 10)
    assert coeffs is not None
    assert coeffs[-1] == __import__("sympy").Rational(1627, 518400)   # leading coeff = volume


def test_non_tree_rejected():
    # the tree-DP requires E = n - 1; a cycle (E = n) must be rejected, not silently miscounted
    import pytest
    with pytest.raises(ValueError):
        matching_polytope_ehrhart(3, [(0, 1), (1, 2), (2, 0)], 2)


def test_probe_no_period_23():
    probe = EhrhartBGProbe()
    # the modulus 23 never appears as the Ehrhart period; the minimal period is 1 for every s
    assert all(probe.minimal_ehrhart_period(s) == 1 for s in probe.s_values)
    assert probe.is_integral_family()
    assert probe.deficit_zero_at_tie()          # Phi^11 = 1 exactly at the tie s=5


def test_probe_check_certifies_negative_result():
    assert EhrhartBGProbe().check()
    assert "NEGATIVE" in EhrhartBGProbe().finding()
    assert EhrhartBGProbe().dp_matches_bruteforce()
