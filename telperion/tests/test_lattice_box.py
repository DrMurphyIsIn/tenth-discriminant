"""Dimensional-lift (LatticeBox) tests: 1D->2D crux families."""
import sys
from fractions import Fraction as Fr
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.bg import LatticeBoxCertificate, near_star_R  # noqa: E402

ARM = Fr(64,621)*Fr(3,2)**11*Fr(64,621); LEAF = Fr(64,621)
def phi2d(x):
    k1,k2=x; S=Fr(k1,3)+k2; d=k1+k2+1; z=Fr(3,3*d)
    return Fr(64,621)*(1+z*S)**11*ARM**k1*LEAF**k2

def test_1d_near_star_lift():
    c = LatticeBoxCertificate("ns1d", 1, lambda x: near_star_R(x[0]), (5,), Fr(1))
    assert c.check()

def test_2d_arms_leaves_crosses():
    c = LatticeBoxCertificate("al2d", 2, phi2d, (5,2), Fr(1))
    assert c.check()                                   # base box + both monotone tails

def test_2d_max_on_1d_face():
    c = LatticeBoxCertificate("al2d", 2, phi2d, (5,2), Fr(1))
    mx, argmax, pinned = c.extremal_face()
    assert mx == 1 and argmax == [(5,0)] and pinned == (1,)   # reduces to near-star edge

def test_lean_emits_base_box():
    c = LatticeBoxCertificate("al2d", 2, phi2d, (5,2), Fr(1))
    lean = c.lean()
    assert "norm_num" in lean and "box_5_0" in lean and "= 1" in lean
