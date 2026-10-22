"""Tests for telperion.arb_fakes (WALL-2 calibration fakes: EP5, EPQ2, DH).

conjecture1_proved = False.
"""
from fractions import Fraction as F

import pytest

flint = pytest.importorskip("flint")

from telperion import arb_dh  # noqa: E402
from telperion.arb_fakes import (  # noqa: E402
    _fe_selfcheck, certify_zero_box, enclose_li_fake, fake_eval, right_halfplane_nonvanishing,
    rigorous_winding,
)


@pytest.mark.parametrize("name", ["zeta", "EP5", "EPQ2", "DH"])
def test_functional_equation(name):
    assert _fe_selfcheck(name) < 1e-30


def test_dh_matches_arb_dh():
    a = fake_eval("DH", "4/5", "857/10")
    b = arb_dh.dh_eval("4/5", "857/10")
    assert a[0] <= b[1] and b[0] <= a[1] and a[2] <= b[3] and b[2] <= a[3]


def test_ep5_first_offline_zero_box():
    c = certify_zero_box("EP5", "923/1000", "943/1000", "7829/500", "7839/500", expected=1)
    assert c["winding"] == 1 and c["off_line"] and c["trust_class"] == "arb"


def test_wrong_count_refused():
    with pytest.raises(ValueError):
        certify_zero_box("EP5", "923/1000", "943/1000", "7829/500", "7839/500", expected=0)


def test_li_zeta_matches_li_coeff():
    from telperion.li_coeff import enclose_li_coeffs
    a = enclose_li_fake("zeta", 20, 256)
    b = enclose_li_coeffs(20, 256)
    assert all(x[0] <= y[1] and y[0] <= x[1] for x, y in zip(a, b))


def test_dominant_term():
    assert right_halfplane_nonvanishing("EP5", "8/5")["certified"]
    assert not right_halfplane_nonvanishing("EPQ2", "8/5")["certified"]   # needs sigma >= 5/2
    assert right_halfplane_nonvanishing("EPQ2", "5/2")["certified"]


def test_node_sampling_undercount_vs_rigorous(monkeypatch):
    """SOUNDNESS FINDING (2026-10-14): arb_dh.winding_number samples only boundary nodes, so two zeros
    close to an edge between nodes are invisible.  f = (z-a)(z-b), both inside: true count 2,
    node sampling returns 1 (at n_per_side 24 AND 48); rigorous_winding returns 2."""
    from flint import acb, acb_series, arb, ctx
    from telperion.arb_fakes import _frac_interval
    a = (F(51, 100), F(1, 10**4))
    b = (F(51, 100) + F(1, 10**5), F(2, 10**4))

    def f(s):
        return (s - acb(arb(f"{a[0]}"), arb(f"{a[1]}"))) * (s - acb(arb(f"{b[0]}"), arb(f"{b[1]}")))

    def ev(x, y, prec=128):
        ctx.prec = prec
        v = f(acb_series([acb(arb(f"{F(x)}"), arb(f"{F(y)}"))])).coeffs()[0]
        return (*_frac_interval(v.real), *_frac_interval(v.imag))

    monkeypatch.setattr(arb_dh, "dh_eval", ev)
    # after fix/arb-winding-rigor, winding_number delegates to the rigorous method; the node sampler keeps
    # the name winding_number_sampled_heuristic.  Fall back to the old name on bases without the fix.
    sampled = getattr(arb_dh, "winding_number_sampled_heuristic", None) or arb_dh.winding_number
    assert sampled(0, 1, 0, 1, prec=128, n_per_side=24) == 1
    assert sampled(0, 1, 0, 1, prec=256, n_per_side=48) == 1
    assert rigorous_winding(f, 0, 1, 0, 1, prec=128) == 2


def test_pole_guard():
    """A box whose closure contains the declared pole s = 1 is refused unless the pole is passed explicitly."""
    from telperion.arb_fakes import count_offline
    with pytest.raises(ValueError, match="pole"):
        certify_zero_box("EP5", "1/2", "3/2", "-1/2", "1/2", expected=0)
    with pytest.raises(ValueError, match="pole"):
        count_offline("EP5", "3/5", "8/5", "0", "5", cuts=[])   # pole on the bottom edge (closure)
    # acknowledged: winding = zeros - poles; EP5 has no zeros near s = 1, so the zero count is 0
    c = certify_zero_box("EP5", "9/10", "11/10", "-1/10", "1/10", expected=0, poles=[(1, 0)])
    assert c["winding"] == -1 and c["zeros_in_box"] == 0
    # DH is entire: no guard
    assert certify_zero_box("DH", "9/10", "11/10", "-1/10", "1/10", expected=0)["winding"] == 0


def test_rigorous_winding_pole_guard():
    """rigorous_winding itself refuses a closed box containing a declared pole unless it is acknowledged
    strictly inside; then it returns zeros - poles.  Default poles=() keeps pole-free callers unchanged."""
    with pytest.raises(ValueError, match="pole"):
        rigorous_winding("EP5", "9/10", "11/10", "-1/10", "1/10")
    with pytest.raises(ValueError, match="pole"):
        rigorous_winding("EP5", "1", "11/10", "-1/10", "1/10", poles=[(1, 0)])   # pole on the boundary
    assert rigorous_winding("EP5", "9/10", "11/10", "-1/10", "1/10", poles=[(1, 0)]) == -1
    assert rigorous_winding("EP5", "923/1000", "943/1000", "7829/500", "7839/500") == 1


def test_wide_box_left_of_zero_does_not_crash():
    """Arb's Hurwitz-zeta series is non-finite on wide balls at Re s < 0 (WALL-6 Q4).  A non-finite segment
    enclosure must make the segment fail (bisect), not crash.  The box [-0.6, 0.4] x [10, 20] is the mirror of
    [0.6, 1.6] x [10, 20] under s -> 1 - conj(s), so by the functional equation both windings agree."""
    w_left = rigorous_winding("EP5", "-0.6", "0.4", "10", "20")
    w_right = rigorous_winding("EP5", "0.6", "1.6", "10", "20")
    assert w_left == w_right >= 1
