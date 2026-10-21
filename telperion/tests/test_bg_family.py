"""Brualdi-Goldwasser (a, b, nu) family certificate — base-cell brick + reduction.

The heterogeneous BG master inequality reduces (vertex/majorization lemma) to the
2-integer + 1-real family GS(a, b, nu); an exact scan collapses that to three
bricks — a Bernstein base cell plus monotone-in-a and monotone-in-b — giving
GS(a, b, nu) <= GS(0, 0, nu) <= T for all a, b >= 0.  These tests exercise the
Telperion-native brick (the base cell) and re-derive the monotone reduction
self-contained in exact `Fraction` arithmetic (no proof/ dependency).
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

# --- kernel-matched exact constants (mirror HomogMasterAssembled.lean) --------
_W = Fr(64, 621)
_GAMMA = _W ** 2 * Fr(5, 3) ** 11
_T = _W * Fr(5, 3) ** 11
_KNEE = Fr(37, 120)
_HALF = Fr(1, 2)


def _glemma(mu: Fr) -> Fr:
    return _GAMMA / (1 + mu / 3) ** 11


def _base_het(j: int, S: Fr) -> Fr:
    d = j + 1
    return (3 * d + 3 * S + 1) / (3 * d)


def _GS_family(a: int, b: int, nu: Fr) -> Fr:
    """GS(a, b, nu) = base(a+b+1, a*knee + b/2 + nu)^11 * glemma(1/2)^b * glemma(nu)."""
    j = a + b + 1
    S = a * _KNEE + b * _HALF + nu
    return _base_het(j, S) ** 11 * _glemma(_HALF) ** b * _glemma(nu)


def _base_cell_poly():
    """0 <= T*(1+nu/3)^11 - GAMMA*base(1,nu)^11  <=>  GS(0,0,nu) <= T."""
    nu = sp.Symbol("nu")
    base1 = (7 + 3 * nu) / sp.Integer(6)
    Ts, Gs = sp.Rational(_T.numerator, _T.denominator), sp.Rational(_GAMMA.numerator, _GAMMA.denominator)
    return sp.expand(Ts * (1 + nu / 3) ** 11 - Gs * base1 ** 11), nu


def test_base_cell_certifies_at_bernstein_elevation_11():
    p, nu = _base_cell_poly()
    assert sp.Poly(p, nu).degree() == 11
    cert = find_bernstein_certificate(p, _KNEE, _HALF, nu, n_max=11)
    assert cert is not None, "base cell must certify (nonneg Bernstein coefficients)"
    n, betas = cert
    assert n == 11 and all(b >= 0 for b in betas)


def test_base_cell_is_the_family_max_via_monotone_reduction():
    # base cell (0,0,nu)/T stays strictly below 1 on [knee, 1/2]; the tie is at
    # the arm (mu=1 leaf), outside this family.
    mx = max(_GS_family(0, 0, _KNEE + (_HALF - _KNEE) * Fr(p, 240)) / _T for p in range(241))
    assert mx < 1 and float(mx) == 0.8722040852637085
    # monotone-decreasing in a and in b => GS(a,b,nu) <= GS(0,0,nu) for all a,b.
    for a in range(12):
        for b in range(12):
            for p in range(61):
                nu = _KNEE + (_HALF - _KNEE) * Fr(p, 60)
                assert _GS_family(a + 1, b, nu) <= _GS_family(a, b, nu)
                assert _GS_family(a, b + 1, nu) <= _GS_family(a, b, nu)


def test_false_bound_is_refused():
    # claim GS(0,0,nu) <= 0.8*T — false (family max is 0.8722*T), so the cleared
    # polynomial goes negative on [knee,1/2] and no nonnegative Bernstein cert exists.
    nu = sp.Symbol("nu")
    base1 = (7 + 3 * nu) / sp.Integer(6)
    T8 = sp.Rational((Fr(4, 5) * _T).numerator, (Fr(4, 5) * _T).denominator)
    Gs = sp.Rational(_GAMMA.numerator, _GAMMA.denominator)
    p_false = sp.expand(T8 * (1 + nu / 3) ** 11 - Gs * base1 ** 11)
    fam = bernstein_family("False", (nu,), GridSpec([("_", [0])]),
                           lambda pt: "false_bound",
                           spec=lambda pt: (p_false, _KNEE, _HALF), n_max=16)
    try:
        certify(fam)
        raised = False
    except Exception:
        raised = True
    assert raised, "a false bound (negative on the interval) must be refused"


def test_emit_is_lint_clean_and_has_heartbeat_budget():
    p, nu = _base_cell_poly()
    fam = bernstein_family("BG", (nu,), GridSpec([("_", [0])]),
                           lambda pt: "bg_family_base_cell",
                           spec=lambda pt: (p, _KNEE, _HALF), n_max=11)
    report = emit(certify(fam), LeanProfile(namespace=("BG",)),
                  [BernsteinEmitter()], ValidationReport(checks=(("bernstein", True),)))
    text = next(iter(report.files.values()))
    # the raw emitter output is search-free (ring + linarith); the example's
    # generate.py adds the heartbeat budget as a local step (tested separately).
    assert "ring" in text and "linarith" in text
    assert "nlinarith" not in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors


def test_generated_example_has_heartbeat_budget_and_is_idempotent():
    import importlib.util
    gen_path = Path(__file__).resolve().parents[1] / "examples" / "bg_family" / "generate.py"
    spec = importlib.util.spec_from_file_location("bg_gen", gen_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    text = mod.build()
    assert "set_option maxHeartbeats" in text
    assert "theorem bg_family_base_cell" in text
    assert mod.main(check=True) == 0            # frozen output matches regeneration


def test_emitter_is_classified_in_the_sensitivity_registry():
    from telperion.emitter_sensitivity import REGISTRY
    assert "BernsteinEmitter" in REGISTRY
