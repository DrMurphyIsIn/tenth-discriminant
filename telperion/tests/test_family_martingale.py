"""Family-adapted martingale bound (Phi^11 < 1 on the tie-recursive family) tests.

This is the strongest POSITIVE statement in the suite: the `<=` half holds strictly on the canonical
`D -> 1` family where every uniform (Knabe) bound fails, via F=1 martingale conservation + a bounded
boundary + an integer ceiling. It is family-adapted -- BG over ALL trees stays open. conjecture1_proved
= False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    TieRecursiveMartingaleCertificate,
    family_ceiling,
    per_block_factor,
    phi11_hub,
    root_amplitude,
)
from telperion.bg.frustration_free import tie_recursive_edges  # noqa: E402
from telperion.bg.rooted_phi import bg_phi11_fast, phi11_rooted  # noqa: E402


def test_per_block_factor_is_exactly_one():
    # (64/621) * (23/18)(3/2)^5 = 1  ->  each block is a tie, zero log-drift (martingale conservation)
    assert per_block_factor() == 1


def test_hub_closed_form_matches_direct_phi():
    # Phi^11_hub(k) = (64/621) a_root(k)^11 equals the directly-computed hub-rooted Phi^11
    for k in range(1, 13):
        n, e = tie_recursive_edges(k)
        assert phi11_hub(k) == phi11_rooted(n, e, 0)


def test_root_amplitude_monotone_and_bounded():
    prev = None
    for k in range(1, 40):
        a = root_amplitude(k)
        assert a < Fr(26, 23)                 # strictly below the sup for every finite k
        if prev is not None:
            assert a > prev                   # strictly increasing
        prev = a
    # the sup 26/23 is the 3/23 cavity fixed point shifted: 1 + 3/23
    assert Fr(26, 23) == 1 + Fr(3, 23)


def test_ceiling_is_integer_inequality_below_one():
    L = family_ceiling()
    assert L == Fr(64, 621) * Fr(26, 23) ** 11
    assert L < 1
    assert 64 * 26 ** 11 < 621 * 23 ** 11     # the integer inequality carrying L < 1


def test_hub_is_maximizer_for_k_ge_3():
    for k in range(3, 8):
        n, e = tie_recursive_edges(k)
        best = max(range(n), key=lambda r: phi11_rooted(n, e, r))
        assert best == 0                      # the central hub is the Phi-maximizing root


def test_family_bound_strict_below_one_including_base_cases():
    L = family_ceiling()
    for k in range(1, 13):
        phi = bg_phi11_fast(*tie_recursive_edges(k))
        assert phi < 1                        # BG holds strictly on the whole family
        if k >= 3:
            assert phi < L                    # ... and is <= the family ceiling for k >= 3


def test_certificate_check_and_scope():
    cert = TieRecursiveMartingaleCertificate()
    assert cert.check()
    f = cert.finding()
    assert "POSITIVE" in f
    assert "conjecture1_proved" in f and "False" in f
    assert "NOT a proof of BG" in f           # honest scope: family-adapted, not general
