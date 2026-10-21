"""The arm maximizes F_B among large-message blocks -- reduced to the master inequality. Tests.

Pins: F_B <= 486/529 for large-message blocks (arm the unique max); the master inequality
(2+mu)^11 F <= (64/621)3^11 for all rooted trees (tight at the leaf); the exact master=>arm telescoping
((1+mu/2)*3/(2+mu)=3/2); and master = 'leaf is the F-maximal child of a mid'. Full master proof is the
remaining crux. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    ArmMaximalCertificate,
    master_upper_bound,
    satisfies_master,
)
from telperion.bg.arm_maximal import F_ARM, MASTER_C  # noqa: E402
from telperion.bg.frustration_free import near_star_edges  # noqa: E402


def test_master_constants_and_leaf_tightness():
    assert MASTER_C == Fr(419904, 23)
    assert F_ARM == Fr(64, 621) ** 2 * Fr(3, 2) ** 11 == Fr(486, 529)
    assert master_upper_bound(Fr(1)) == Fr(64, 621)     # leaf: master bound is tight
    leaf = (1, (), 0)
    assert satisfies_master(*leaf)                       # leaf saturates the master inequality


def test_master_holds_on_representative_trees():
    for s in (2, 3, 4, 5):
        n, e = near_star_edges(s)
        assert satisfies_master(n, e, 0)                 # near-stars satisfy master


def test_master_telescopes_to_arm_exactly():
    cert = ArmMaximalCertificate()
    assert cert.master_telescopes_to_arm()               # (1+mu/2)*3/(2+mu)=3/2, (64/621)^2(3/2)^11=486/529
    assert cert.master_is_leaf_maximal_child()           # MASTER_C = 486/529 * 2^11 * 621/64


def test_arm_maximizes_F_over_census():
    cert = ArmMaximalCertificate(census_m=7)
    assert cert.arm_maximizes_F_among_large_message()
    assert cert.master_inequality_on_census()


def test_certificate_check_and_scope():
    cert = ArmMaximalCertificate(census_m=7)
    assert cert.check()
    f = cert.finding()
    assert "master" in f.lower() and "486/529" in f
    assert "conjecture1_proved = False" in f
