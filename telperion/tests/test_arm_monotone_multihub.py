"""R1 (arm monotonicity, single-hub) + R2 (multi-hub extremality) tests.

R1: message-vs-Phi^11 monotonicity closes chains (arm = max path) and leaf-child blocks; residual =
all-non-leaf branching. R2: near-star maximizes Phi^11 only at odd n (two-hub wins at even n), so
single-hub extremality does not lift; global max = the tie. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    ArmMonotoneCertificate,
    MultiHubExtremalityCertificate,
    chain_link_factor,
    is_near_star,
    path_F,
    phi_maximizer,
)
from telperion.bg.frustration_free import near_star_edges  # noqa: E402


# --- R1: single-hub monotonicity ---
def test_chain_contraction_and_arm_max_path():
    assert chain_link_factor(Fr(1, 3)) < 1                 # each chain link contracts F
    assert path_F(2) == Fr(486, 529)                       # the arm P_2 is the max path
    assert path_F(3) < path_F(2) and path_F(4) < path_F(3)  # F decreasing along the chain


def test_R1_certificate():
    cert = ArmMonotoneCertificate(census_m=7)
    assert cert.check()
    assert cert.chain_contraction_holds()
    assert cert.leaf_child_blocks_bounded()
    assert cert.residual_is_all_nonleaf_branching()        # the residual genuinely exists
    assert "monotonicity" in cert.finding()


# --- R2: multi-hub extremality ---
def test_near_star_detection():
    n, e = near_star_edges(5)
    assert is_near_star(n, e)
    assert not is_near_star(6, ((0, 1), (1, 2), (2, 3), (3, 4), (4, 5)))   # a path is not a near-star


def test_parity_alternating_extremal():
    # odd n: near-star maximizes; even n: multi-hub wins
    for n in (5, 7):
        _best, arg = phi_maximizer(n)
        assert is_near_star(n, arg)
    for n in (4, 6):
        _best, arg = phi_maximizer(n)
        assert not is_near_star(n, arg)


def test_R2_certificate_and_scope():
    cert = MultiHubExtremalityCertificate(odd_ns=(5, 7), even_ns=(4, 6, 8))
    assert cert.check()
    assert cert.global_max_is_the_tie()
    f = cert.finding()
    assert "PARITY-ALTERNATING" in f
    assert "conjecture1_proved = False" in f
