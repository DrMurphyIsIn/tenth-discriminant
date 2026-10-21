"""Bridge-crossing (near-star span) tests."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.bg import NearStarBridgeCertificate, near_star_R, near_star_tail_poly  # noqa: E402

def test_near_star_tie_and_base():
    assert near_star_R(5) == 1
    for k in range(5):
        assert near_star_R(k) < 1
    assert near_star_R(6) < 1

def test_tail_all_nonneg_coeffs():
    _, nonneg = near_star_tail_poly(5)
    assert nonneg                                    # Polya-trivial monotone tail

def test_bridge_certificate_crosses():
    c = NearStarBridgeCertificate(anchor=5)
    assert c.check()
    lean = c.lean()
    assert "near_star_tail" in lean and "positivity" in lean and "norm_num" in lean

def test_continuous_relaxation_exceeds_one():
    # the certificate is genuinely integer-only: R_cont > 1 somewhere
    rc = lambda s: (64/621)**(2*s+1) * 1.5**(11*s) * ((4*s+3)/(3*(s+1)))**11
    assert max(rc(4 + i/100) for i in range(200)) > 1
