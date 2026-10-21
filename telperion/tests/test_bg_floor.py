"""Brualdi-Goldwasser R7 ledger-floor certificate — chain class (a=0, nl=0, m=1).

R7 hardens the slack-ledger context-free floors: per-node slack(y) >= class floor
on the equal-children cavity y in (0,1/2].  This example emits the CHAIN class
(floor 27/5000) as a clean two-cell Bernstein certificate, bracketing the
transcendentals (L, log(1+u), T0) by verified rationals from the BG kernel.  These
tests check both hinge cells certify, that they cover [0,1/2], that the rational
brackets are valid (so slack_lb <= slack), and that too-high a floor is refused.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import (  # noqa: E402
    BernsteinEmitter, ValidationReport, certify, emit, find_bernstein_certificate,
)
from telperion.emit_bernstein import bernstein_family  # noqa: E402
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_L_LO = sp.Rational(206586, 10**6)
_T_LO = sp.Rational(2294736, 10**7)
_C = sp.Rational(11, 50)
_FLOOR = sp.Rational(27, 5000)
_HALF = sp.Rational(1, 2)
_Y = sp.Symbol("y")


def _slack_lb(cell):
    u = _Y / 2
    log_ub = u - u**2 / 2 + u**3 / 3 - u**4 / 4 + u**5 / 5
    if cell == 0:                                   # I1 = [0, T_LO]
        return _L_LO - log_ub - _C * (1 / (2 + _Y) - _T_LO), sp.Integer(0), _T_LO
    return _L_LO - log_ub - _C * (1 / (2 + _Y) - _Y), _T_LO, _HALF   # I2 = [T_LO, 1/2]


def _num(cell):
    expr, lo, hi = _slack_lb(cell)
    return sp.expand(sp.fraction(sp.together(expr - _FLOOR))[0]), lo, hi


def test_both_hinge_cells_bernstein_certify():
    for cell in (0, 1):
        p, lo, hi = _num(cell)
        assert sp.Poly(p, _Y).degree() == 6
        cert = find_bernstein_certificate(p, lo, hi, _Y, n_max=16)
        assert cert is not None, f"cell {cell} must certify (nonneg Bernstein coeffs)"


def test_cells_cover_the_cavity_range():
    # I1 = [0, T_LO], I2 = [T_LO, 1/2] tile [0, 1/2] with no gap.
    _, lo0, hi0 = _num(0)
    _, lo1, hi1 = _num(1)
    assert lo0 == 0 and hi0 == lo1 == _T_LO and hi1 == _HALF


def test_rational_brackets_are_valid_so_slack_lb_is_a_true_lower_bound():
    # log(1+u) <= u - u^2/2 + u^3/3 - u^4/4 + u^5/5 on u in (0, 1/4]  (=> slack_lb <= slack)
    u = sp.Symbol("u")
    log_ub = u - u**2 / 2 + u**3 / 3 - u**4 / 4 + u**5 / 5
    import math
    for t in range(1, 101):
        uv = 0.25 * t / 100
        assert float(log_ub.subs(u, uv)) >= math.log(1 + uv) - 1e-15
    # L_LO <= L = log(621/64)/11
    assert float(_L_LO) <= math.log(621 / 64) / 11


def test_slack_lb_stays_at_or_above_floor_on_both_cells():
    for cell in (0, 1):
        expr, lo, hi = _slack_lb(cell)
        mn = min(float((expr - _FLOOR).subs(_Y, lo + (hi - lo) * Fr(t, 200))) for t in range(201))
        assert mn >= 0, f"cell {cell} slack_lb dips below floor ({mn})"


def test_too_high_a_floor_is_refused():
    # the chain floor is tight (~0.0055); claiming slack >= 0.01 is false near y=1/2.
    u = _Y / 2
    log_ub = u - u**2 / 2 + u**3 / 3 - u**4 / 4 + u**5 / 5
    expr = _L_LO - log_ub - _C * (1 / (2 + _Y) - _Y)
    p_false = sp.expand(sp.fraction(sp.together(expr - sp.Rational(1, 100)))[0])
    fam = bernstein_family("FalseFloor", (_Y,), GridSpec([("_", [0])]),
                           lambda pt: "false_floor",
                           spec=lambda pt: (p_false, _T_LO, _HALF), n_max=20)
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "a floor above the tight true minimum must be refused"


def test_emit_is_lint_clean_and_search_free():
    p0, lo0, hi0 = _num(0)
    fam = bernstein_family("BGF", (_Y,), GridSpec([("_", [0])]),
                           lambda pt: "bg_floor_chain_below_knee",
                           spec=lambda pt: (p0, lo0, hi0), n_max=16)
    report = emit(certify(fam), LeanProfile(namespace=("BGF",)),
                  [BernsteinEmitter()], ValidationReport(checks=(("bernstein", True),)))
    text = next(iter(report.files.values()))
    assert "ring" in text and "linarith" in text and "nlinarith" not in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_generated_example_is_idempotent_with_heartbeat_budget():
    import importlib.util
    gen = Path(__file__).resolve().parents[1] / "examples" / "bg_floor" / "generate.py"
    spec = importlib.util.spec_from_file_location("bgfloor_gen", gen)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    text = mod.build()
    assert text.count("set_option maxHeartbeats") == 2
    assert mod.main(check=True) == 0


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "BernsteinEmitter" in REGISTRY
