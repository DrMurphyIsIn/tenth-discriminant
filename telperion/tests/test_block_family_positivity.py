"""Safe-hub family positivity: BG's <= half on an infinite class of single-hub families.

Pins the theorem (F_B<=1 and (1+mu)^11<=621/64 => Phi^11_hub(k)<1 for all k), verified on the block
census, with the tie-recursive family a special case and the near-star the boundary. A real piece of the
<= half; NOT all of BG (large-message/dangerous-hub case open). conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    SafeHubFamilyCertificate,
    block_is_safe_hub,
    family_phi,
    is_safe_message,
    safe_hub_ceiling,
)
from telperion.bg.frustration_free import near_star_edges  # noqa: E402


def test_safe_message_and_ceiling():
    assert is_safe_message(Fr(3, 23))                       # tie block: (26/23)^11 < 621/64
    assert not is_safe_message(Fr(1, 3))                    # arm block: (4/3)^11 > 621/64
    assert safe_hub_ceiling(Fr(3, 23)) == Fr(64, 621) * Fr(26, 23) ** 11   # = family_martingale's L
    assert safe_hub_ceiling(Fr(3, 23)) < 1


def test_tie_block_is_safe_hub_and_family_bounded():
    n, e = near_star_edges(5)
    assert block_is_safe_hub(n, e, 0)
    for k in (1, 2, 3, 5, 10, 20):
        assert family_phi(n, e, 0, k) < 1                  # tie-recursive family: BG holds


def test_arm_block_not_safe_and_reaches_one():
    arm = (2, ((0, 1),), 0)
    assert not block_is_safe_hub(*arm)                     # large message -> not safe-hub
    assert family_phi(*arm, 5) == 1                        # near-star tie at k=5 (the boundary)


def test_theorem_holds_on_census():
    cert = SafeHubFamilyCertificate(census_m=6)
    res = cert.theorem_holds_on_census()
    assert res is not None                                 # theorem holds on all safe-hub blocks
    safe, total = res
    assert 0 < safe < total                                # a broad but proper subclass


def test_certificate_check_and_scope():
    cert = SafeHubFamilyCertificate(census_m=6)
    assert cert.check()
    f = cert.finding()
    assert "THEOREM" in f and "infinite-class" in f
    assert "conjecture1_proved = False" in f
