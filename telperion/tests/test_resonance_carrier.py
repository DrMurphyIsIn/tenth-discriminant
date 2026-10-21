"""Resonance carrier (the 23-adic |Phi^11|_23 both Tier-B probes redirect to) tests.

Pins the verified identities/lemmas: the adelic product formula, the tie as a 23-adic unit,
categorical strictness Phi^11 != 1 on 11 \\nmid n, and the widening 23-adic gap off the tie.
These are real -- BG itself is NOT proved (the 11 | n core stays open). conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    ResonanceCarrierCertificate,
    adelic_product,
    phi11_23adic_size,
    phi11_23adic_valuation,
)
from telperion.bg.matching_free_energy import near_star_edges  # noqa: E402
from telperion.bg.sporadic_tie import amp_product  # noqa: E402
from telperion.padic import padic_val_frac  # noqa: E402


def test_delta_matches_amplitude_form():
    # v_23(Phi^11) == 11 * v_23(prod a_v) - n  (the amplitude-form identity), at the tie and off it
    for s in (3, 4, 5, 6):
        n, e = near_star_edges(s)
        # amp_product is root-dependent; the BG value is the max-root one. For near-stars root 0 (hub)
        # realizes the maximizer, matching bg_phi11; verify the identity there.
        direct = phi11_23adic_valuation(n, e)
        amp = 11 * padic_val_frac(amp_product(n, e, 0), 23) - n
        assert direct == amp


def test_tie_is_23adic_unit():
    n, e = near_star_edges(5)          # N(0,5), n = 11, the tie
    assert phi11_23adic_valuation(n, e) == 0
    assert phi11_23adic_size(n, e) == 1


def test_gap_widens_off_tie_on_near_stars():
    # off-tie near-stars: delta = -n, so |Phi^11|_23 = 23^n > 1, growing with s
    for s in (2, 3, 4, 6, 7):
        n, e = near_star_edges(s)
        assert phi11_23adic_valuation(n, e) == -n
        assert phi11_23adic_size(n, e) == Fr(23) ** n
    # the tie is the lone |.|_23 = 1
    n5, e5 = near_star_edges(5)
    assert phi11_23adic_size(n5, e5) == 1


def test_adelic_product_formula():
    # prod_v |Phi^11|_v = 1 for a spread of near-stars (tie included) -- the adelic identity
    for s in (2, 3, 4, 5, 6):
        n, e = near_star_edges(s)
        assert adelic_product(n, e) == 1


def test_categorical_strictness_needs_11_divides_n():
    # for 11 \nmid n the 23-adic valuation is never 0 -> Phi^11 != 1 for an arithmetic reason
    cert = ResonanceCarrierCertificate(n_max=9)
    assert cert.categorical_strictness_off_11()


def test_certificate_check_and_finding():
    cert = ResonanceCarrierCertificate(n_max=9)
    assert cert.check()
    assert cert.product_formula_holds()
    assert cert.tie_is_23adic_unit()
    assert cert.gap_widens_off_tie()
    f = cert.finding()
    assert "conjecture1_proved = False" in f
    # honest scope: does NOT claim to close the 11 | n core
    assert "irreducible core" in f
    assert "lean" in dir(cert)
