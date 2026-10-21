"""Tier-C #1 probe: tree matching polynomial as a discrete/arithmetic Gaussian (Lorentzian) -- tests.

Pins the exact obstruction: the non-separable per-edge matching polynomial fails M-convexity (matchings are
a delta-matroid), while the Lorentzian bivariate m_k object is separable and generic -- so the naive route
carries neither non-separable+integral together nor localizes the tie. A reasoned negative that corrects the
literature-push proposal. conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    MatchingLorentzianProbe,
    bivariate_matching_is_lorentzian,
    matching_support_vectors,
    matchings,
    support_is_m_convex,
)
from telperion.bg.frustration_free import near_star_edges  # noqa: E402


def test_m_convexity_test_on_known_sets():
    # a simplex face {(2,0),(1,1),(0,2)} is M-convex; a "hole" set is not
    assert support_is_m_convex([(2, 0, 0), (1, 1, 0), (1, 0, 1), (0, 1, 1)])
    assert not support_is_m_convex([(2, 0, 0), (0, 2, 0), (0, 0, 2)])   # no exchange path


def test_matchings_enumeration():
    n, e = near_star_edges(2)                      # hub 0, arms (0,1)-(1,2), (0,3)-(3,4); 4 edges
    Ms = matchings(n, e)
    assert frozenset() in Ms                       # empty matching included
    assert max(len(M) for M in Ms) == 2            # max matching = 2


def test_multivariate_matching_support_not_m_convex():
    # the per-edge (non-separable) matching polynomial fails M-convexity -> NOT Lorentzian
    for s in (2, 3, 4):
        n, e = near_star_edges(s)
        assert not support_is_m_convex(matching_support_vectors(n, e))


def test_bivariate_m_k_is_lorentzian_but_generic():
    # the bivariate m_k object IS Lorentzian (real-rooted) for every near-star, incl. the tie -> generic
    for s in (2, 3, 4, 5):
        n, e = near_star_edges(s)
        assert bivariate_matching_is_lorentzian(n, e)


def test_probe_check_and_finding():
    probe = MatchingLorentzianProbe()
    assert probe.check()
    assert probe.multivariate_support_not_m_convex()
    assert probe.bivariate_is_lorentzian_and_generic()
    assert probe.tie_not_localized_by_lorentzian_membership()
    f = probe.finding()
    assert "delta-matroid" in f
    assert "conjecture1_proved = False" in f
