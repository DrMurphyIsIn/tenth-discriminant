"""The branching (j'>=2) g-step optimization, reduced to two rational leaves. Tests.

Pins: symmetric-argmax (global max is symmetric); per-j' max at the crossover mu*; boost(mu*) < 4/3 (from
3 mu* < 1); the two exact rational leaves (I) gamma < (10/9)^11 (mu*<1/3) and (II) W(4/3)^11 < gamma, and
their cross-multiplied integer forms; and that they bound the optimization below gamma. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    GStepReductionCertificate,
    MU_STAR,
    f_sym,
    leaf_W_four_thirds_lt_gamma,
    leaf_mu_star_lt_third,
)
from telperion.bg.gstep_reduction import GAMMA, W  # noqa: E402


def test_rational_leaves_exact():
    assert leaf_mu_star_lt_third()                                   # gamma < (10/9)^11  (mu* < 1/3)
    assert GAMMA < Fr(10, 9) ** 11
    assert 64 ** 2 * 5 ** 11 * 9 ** 11 < 621 ** 2 * 3 ** 11 * 10 ** 11
    assert leaf_W_four_thirds_lt_gamma()                             # W(4/3)^11 < gamma
    assert 621 * 4 ** 11 < 64 * 5 ** 11
    assert MU_STAR < 1 / 3


def test_leaves_chain_below_gamma():
    # f_{j'>=2}(mu*) = W*boost^11 < W*(4/3)^11 < gamma ; binding j'=2 value ~2.107
    assert float(W * Fr(4, 3) ** 11) < float(GAMMA)
    assert f_sym(2, MU_STAR) < float(W * Fr(4, 3) ** 11)
    assert f_sym(2, MU_STAR) < float(GAMMA)


def test_coordinate_wise_reduction_and_scope():
    cert = GStepReductionCertificate()
    assert cert.box_max_is_symmetric_mustar()     # Schur-convex, but global max IS symmetric mu*
    assert cert.t1_increasing_below_mustar()
    assert cert.t2_descent_engine()               # the rational (j'+1)*boost >= 3+mu engine
    assert cert.boost_star_below_four_thirds()
    assert cert.rational_leaves()
    assert cert.check()
    f = cert.finding()
    assert "COORDINATE-WISE UNIMODALITY" in f and "NOT majorization" in f
    assert "Schur-CONVEX" in f
    assert "621*4^11 < 64*5^11" in f
    assert "conjecture1_proved = False" in f


def test_descent_engine_and_boost_bound_rational():
    from telperion.bg.gstep_reduction import descent_engine_holds, boost_le_four_thirds_when_small
    # T2 rational engine: (j+1)*boost >= 3+mu for j>=2, mu<=S
    assert descent_engine_holds(2, Fr(1), Fr(1, 2))
    assert all(descent_engine_holds(j, Fr(sn, 10), Fr(min(sn, 5), 10))
               for j in range(2, 8) for sn in range(0, 5 * j + 1))
    # boost <= 4/3 when 3S <= j (tight at 3S = j)
    assert boost_le_four_thirds_when_small(3, Fr(1)) and (1 + Fr(3 * 1 + 1, 3 * 3 + 3)) == Fr(4, 3)
