"""R2 refinement -- the multi-hub extremal is the double near-star, bounded away from 1. Tests.

Pins: DN(4,5) is the DN-family peak with Phi^11 = 0.85238 < 1; the double near-star is the exhaustive
multi-hub maximizer for small n; more hubs give lower peaks; perturbing the tie into a second hub collapses
Phi^11. So BG's equality is exclusively single-hub. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    DoubleNearStarCertificate,
    dns_phi11,
    double_near_star_edges,
    multi_hub_peak,
)


def test_double_near_star_shape_and_peak():
    n, e = double_near_star_edges(2, 3)
    assert n == 2 + 2 * (2 + 3)                       # n = 2 + 2(a+b)
    peak, ab, pn = multi_hub_peak(9)
    assert ab == (4, 5) and pn == 20                  # the DN family peaks at DN(4,5), n=20
    assert peak == dns_phi11(4, 5)
    assert peak < 1 and float(peak) > 0.85            # a clean gap below 1


def test_gap_is_structural():
    cert = DoubleNearStarCertificate(max_n=13)
    assert cert.more_hubs_lower_peak()                # 2-hub peak > 3-hub peak
    assert cert.tie_perturbation_collapses()          # tie -> 2 hubs drops Phi^11 well below 1


def test_R2_refinement_certificate_and_scope():
    cert = DoubleNearStarCertificate(max_n=13)
    assert cert.check()
    assert cert.dns_is_multi_hub_max()                # DN is the exhaustive multi-hub max for n<=13
    assert cert.peak_below_one()
    f = cert.finding()
    assert "DOUBLE NEAR-STAR" in f
    assert "EXCLUSIVELY the single-hub tie" in f
    assert "conjecture1_proved = False" in f
