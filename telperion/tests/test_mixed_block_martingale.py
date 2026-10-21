"""Mixed-block martingale (per-block transfer factor + generalized hub bound) tests.

Pins the verified structure: the general formula, the no-supercritical-block census (BG-necessary),
the tie as the unique 23-gated marginal block, and the near-star as the extremal single-hub family.
BG itself is NOT proved -- F_b <= 1 for ALL blocks / interior maxima / multi-level trees stay open.
conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    MixedBlockMartingaleCertificate,
    block_amplitude_and_message,
    block_factor,
    build_hub_tree,
    homogeneous_family_phi11,
    homogeneous_family_sup,
    hub_phi11,
)
from telperion.bg.frustration_free import near_star_edges, tie_recursive_edges  # noqa: E402
from telperion.bg.rooted_phi import phi11_rooted  # noqa: E402

ARM = (2, ((0, 1),), 0)                 # length-2 arm (mid-leaf): the near-star's block
TIE = (near_star_edges(5)[0], near_star_edges(5)[1], 0)


def test_general_formula_matches_direct_phi_on_mixed_hub():
    specs = [(3, ((0, 1), (1, 2)), 0), (4, ((0, 1), (0, 2), (0, 3)), 0), ARM]
    n, e = build_hub_tree(specs)
    assert hub_phi11(specs) == phi11_rooted(n, e, 0)


def test_arm_block_factor_and_message():
    alpha, mu = block_amplitude_and_message(*ARM)
    assert alpha == Fr(3, 2) and mu == Fr(1, 3)
    assert block_factor(*ARM) == Fr(486, 529)      # = the fractal-tail factor


def test_tie_block_is_marginal():
    assert block_factor(*TIE) == 1
    _, mu = block_amplitude_and_message(*TIE)
    assert mu == Fr(3, 23)                          # the cavity fixed point


def test_arm_family_reproduces_near_star_and_peaks_at_the_tie():
    # hub + k arm blocks == N(0,k); the family peaks at exactly Phi^11 = 1 at k = 5 (the tie)
    for k in (2, 3, 5, 7):
        n, e = near_star_edges(k)
        assert homogeneous_family_phi11(*ARM, k) == phi11_rooted(n, e, 0)
    kstar, sup = homogeneous_family_sup(*ARM)
    assert kstar == 5 and sup == 1


def test_tie_recursive_family_is_marginal_blocks():
    # the family_martingale family = hub + k tie-blocks; homogeneous formula matches its hub-rooted Phi
    for k in (1, 2, 3, 5):
        n, e = tie_recursive_edges(k)
        assert homogeneous_family_phi11(*TIE, k) == phi11_rooted(n, e, 0)


def test_no_supercritical_block_in_census():
    # F_b <= 1 for every rooted block up to n_b = 9 (BG-necessary: no block drives Phi^11_hub -> inf)
    cert = MixedBlockMartingaleCertificate(supercritical_census_max=9)
    assert cert.no_supercritical_block()


def test_marginal_first_at_11_and_no_family_exceeds_one():
    cert = MixedBlockMartingaleCertificate(family_census_max=7)
    assert cert.marginal_first_appears_at_11()
    assert cert.no_homogeneous_family_exceeds_one()
    assert cert.near_star_is_extremal_family()


def test_certificate_check_and_scope():
    cert = MixedBlockMartingaleCertificate()
    assert cert.check()
    f = cert.finding()
    assert "NECESSARY condition for BG" in f
    assert "Does NOT prove BG" in f and "conjecture1_proved = False" in f
