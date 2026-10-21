"""Sibling coupling (Lewis-Riesenfeld read + single-variable no-go) tests.

Pins: the geometric-mean-amplitude reformulation of BG (equality at the tie), the symmetric-mode
coupling, and the single-variable no-go. The multivariate invariant is NOT constructed and BG is NOT
proved -- the deep-dive frames the open target. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

import pytest

pytest.importorskip("networkx")  # graph enumeration needs networkx; skip cleanly if absent

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    RHO_B_11,
    SiblingCouplingCertificate,
    amplitude_product,
    parent_amplitude,
)
from telperion.bg.frustration_free import near_star_edges  # noqa: E402
from telperion.bg.rooted_phi import phi11_rooted  # noqa: E402


def test_bg_is_geometric_mean_amplitude_bound():
    # (prod a)^11 <= (621/64)^n  <=>  phi11_rooted <= 1
    import networkx as nx
    for m in range(2, 8):
        for T in nx.nonisomorphic_trees(m):
            idx = {v: i for i, v in enumerate(T.nodes())}
            e = tuple((idx[a], idx[b]) for a, b in T.edges())
            for r in range(m):
                assert (amplitude_product(m, e, r) ** 11 <= RHO_B_11 ** m) == (phi11_rooted(m, e, r) <= 1)


def test_tie_saturates_the_amplitude_bound():
    n, e = near_star_edges(5)
    assert amplitude_product(n, e, 0) ** 11 == RHO_B_11 ** n     # equality exactly at the tie


def test_symmetric_mode_coupling():
    # a_v depends on children only through (S, j): distinct multisets, same sum -> same amplitude
    assert parent_amplitude(Fr(1), 3) == parent_amplitude(Fr(1, 3) + Fr(1, 3) + Fr(1, 3), 3)
    assert parent_amplitude(Fr(1), 3) == parent_amplitude(Fr(1, 2) + Fr(1, 4) + Fr(1, 4), 3)
    # sanity: amplitude form reproduces phi
    n, e = near_star_edges(3)
    assert Fr(64, 621) ** n * amplitude_product(n, e, 0) ** 11 == phi11_rooted(n, e, 0)


def test_certificate_check_and_scope():
    cert = SiblingCouplingCertificate(m_max=7)
    assert cert.check()
    assert not cert.single_variable_invariant_ruled_out()   # retracted 2026-09-29
    f = cert.finding()
    assert "RETRACTED" in f
    assert "conjecture1_proved = False" in f
