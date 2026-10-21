"""BG R7 ledger-floor certificates — bare-leaf (nl=1) and nl=2 families.

Extends the chain-class beachhead to the two main context-free ledger classes with
a child cavity y in (0,1/2]: bare-leaf (floor 26/500) over a in 0..9, m in {1,2,3};
nl=2 (floor 54/500) over a in 0..6, m in {1,2,3}.  Each (a,m) splits into two hinge
cells tiling [0,1/2].  These tests check every emitted cell certifies, the class
taxonomy/floors are right, the rational brackets are valid, and a too-high floor is
refused.
"""
import importlib.util
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

_Y = sp.Symbol("y")


def _gen():
    gen = Path(__file__).resolve().parents[1] / "examples" / "bg_floor_families" / "generate.py"
    spec = importlib.util.spec_from_file_location("bgff_gen", gen)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_every_family_cell_bernstein_certifies():
    cells = _gen()._cells()
    assert len(cells) == 102                    # (10*3 + 7*3) combos * 2 cells
    for name, num, lo, hi in cells:
        assert sp.Poly(num, _Y).degree() == 5
        assert find_bernstein_certificate(num, lo, hi, _Y, n_max=13) is not None, name


def test_class_taxonomy_and_names():
    cells = _gen()._cells()
    names = {c[0] for c in cells}
    # bare-leaf: a in 0..9, m in 1..3, below+above
    assert "bg_floor_bareleaf_a0_m1_below" in names
    assert "bg_floor_bareleaf_a9_m3_above" in names
    assert "bg_floor_nl2_a6_m3_above" in names
    assert sum(1 for n in names if "bareleaf" in n) == 60
    assert sum(1 for n in names if "nl2" in n) == 42


def test_rational_brackets_are_valid():
    import math
    mod = _gen()
    assert float(mod._L_LO) <= math.log(621 / 64) / 11          # L_LO <= L
    assert float(mod._G_HI) >= math.log(3 / 2)                  # G_HI >= log(3/2)
    u = sp.Symbol("u")
    log_ub = u - u**2 / 2 + u**3 / 3 - u**4 / 4 + u**5 / 5
    for t in range(1, 101):
        uv = 0.5 * t / 100
        assert float(log_ub.subs(u, uv)) >= math.log(1 + uv) - 1e-12


def test_too_high_a_floor_is_refused():
    # bump the bare-leaf floor from 0.052 to 0.20 (above the ~0.06 worst slack) -> refused
    mod = _gen()
    a, nl, m = 0, 1, 1
    k = a + nl + m
    p = 1 + 2 * a + nl
    S = sp.Rational(a, 3) + nl + m * _Y
    u = S / (k + 1)
    log_ub = u - u**2 / 2 + u**3 / 3 - u**4 / 4 + u**5 / 5
    cav0 = sp.Integer(1) / (k + 1 + sp.Rational(a, 3) + nl)
    Dc = sp.Max(sp.Integer(0), cav0 - mod._T_LO)
    above = p * mod._L_LO - a * mod._G_HI - log_ub - mod._C * (Dc - m * (_Y - mod._T_HI))
    num = sp.expand(sp.fraction(sp.together(above - sp.Rational(1, 5)))[0])
    fam = bernstein_family("FalseFam", (_Y,), GridSpec([("_", [0])]),
                           lambda pt: "false_fam",
                           spec=lambda pt: (num, mod._T_LO, sp.Rational(1, 2)), n_max=20)
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "a floor above the true minimum must be refused"


def test_emit_is_lint_clean_and_search_free():
    cells = _gen()._cells()
    name, num, lo, hi = cells[0]
    fam = bernstein_family("BGFF", (_Y,), GridSpec([("_", [0])]),
                           lambda pt: name, spec=lambda pt: (num, lo, hi), n_max=13)
    report = emit(certify(fam), LeanProfile(namespace=("BGFF",)),
                  [BernsteinEmitter()], ValidationReport(checks=(("bernstein", True),)))
    text = next(iter(report.files.values()))
    assert "ring" in text and "linarith" in text and "nlinarith" not in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_generated_example_is_idempotent_with_heartbeat_budgets():
    mod = _gen()
    text = mod.build()
    assert text.count("set_option maxHeartbeats") == 102
    assert mod.main(check=True) == 0


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "BernsteinEmitter" in REGISTRY
