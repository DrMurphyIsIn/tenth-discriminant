"""Mahler measure & Lehmer-gap probe (Tier-B #1 for Brualdi-Goldwasser) tests.

The finding is NEGATIVE by design; these tests pin the INSTRUMENT (Mahler engine + cyclotomic
detector, validated on Lehmer's polynomial and cyclotomics) and the reproducibility of the
negative result over the near-star family.  conjecture1_proved = False.
"""
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    LEHMER_CONSTANT,
    MahlerLehmerProbe,
    dpa_charpoly,
    is_cyclotomic_product,
    mahler_measure,
    matching_poly,
    matching_poly_from_counts,
)

x = sp.Symbol("x")


def test_mahler_engine_known_values():
    # Lehmer's polynomial: the smallest known Mahler measure above 1
    lehmer = [1, 1, 0, -1, -1, -1, -1, -1, 0, 1, 1]
    assert abs(mahler_measure(lehmer) - LEHMER_CONSTANT) < 1e-9
    # cyclotomics have Mahler measure exactly 1
    assert abs(mahler_measure([1, 1, 1]) - 1.0) < 1e-9          # Phi_3
    assert abs(mahler_measure(sp.Poly(sp.cyclotomic_poly(12, x), x).all_coeffs()) - 1.0) < 1e-9
    # a scaled / non-monic example: 2*(x-3) has M = 2 * 3 = 6
    assert abs(mahler_measure([2, -6]) - 6.0) < 1e-9


def test_cyclotomic_detector():
    assert is_cyclotomic_product(sp.Poly(sp.cyclotomic_poly(5, x), x))
    assert is_cyclotomic_product(sp.Poly(sp.cyclotomic_poly(23, x), x))
    # product of two cyclotomics is still cyclotomic-product
    assert is_cyclotomic_product(sp.Poly(sp.cyclotomic_poly(3, x) * sp.cyclotomic_poly(4, x), x))
    # Lehmer's polynomial is NOT a product of cyclotomics
    assert not is_cyclotomic_product(sp.Poly([1, 1, 0, -1, -1, -1, -1, -1, 0, 1, 1], x))
    # x^2 - 2 (root sqrt 2, off the unit circle) is not
    assert not is_cyclotomic_product(sp.Poly(x ** 2 - 2, x))


def test_matching_poly_two_routes_agree():
    # adjacency-determinant route == k-matching-count assembly, for every near-star in the family
    from telperion.bg.matching_free_energy import near_star_edges
    for s in (2, 3, 4, 5, 6):
        n, edges = near_star_edges(s)
        assert matching_poly(n, edges) == matching_poly_from_counts(n, edges)


def test_dpa_charpoly_is_gaussian_integer_and_monic():
    from telperion.bg.matching_free_energy import near_star_edges
    n, edges = near_star_edges(5)
    dp = dpa_charpoly(n, edges)
    assert dp.degree() == n
    assert dp.all_coeffs()[0] == 1  # monic
    # coefficients live in Z[i]: real and imaginary parts are integers
    for c in dp.all_coeffs():
        assert sp.Rational(sp.re(c)).is_integer and sp.Rational(sp.im(c)).is_integer


def test_no_resonance_at_the_tie():
    probe = MahlerLehmerProbe()
    rows = probe.family_measures()
    by_s = {s: (m_match, m_dpa, cyc) for s, _n, m_match, m_dpa, cyc in rows}
    # the tie s=5 is NOT cyclotomic and NOT Mahler-measure 1
    m_tie, _d, cyc_tie = by_s[5]
    assert not cyc_tie
    assert m_tie > 1.1
    # no near-star's matching polynomial is cyclotomic
    assert all(not cyc for _s, _n, _m, _d, cyc in rows)
    # M(matching) ~ s + 1 and strictly increasing: the tie is unremarkable
    assert probe.matching_measure_monotone()
    assert not probe.tie_is_resonant()


def test_probe_check_certifies_instrument_and_negative_result():
    # check() certifies the instrument + reproducibility of the NEGATIVE result, not BG
    assert MahlerLehmerProbe().check()
    assert MahlerLehmerProbe().instrument_valid()
    assert "NEGATIVE" in MahlerLehmerProbe().finding()
