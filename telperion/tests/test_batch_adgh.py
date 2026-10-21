"""A + D-H batch tests: witness search, sharpness, pilot, cilog, potentials, cone."""
import sys
from pathlib import Path

import pytest
import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    CertificationError,
    GridSpec,
    InequalityFamily,
    certify,
    cone_combination,
    fixed_points,
    per_node_family,
)
from telperion.cilog import parse_log  # noqa: E402
from telperion.interchange import export_certificates  # noqa: E402
from telperion.probe_sharp import sharpness  # noqa: E402

u, v = sp.symbols("u v", nonnegative=True)


# ---- A: witness search ------------------------------------------------------
def _wit_fam():
    # claim: for each a, SOME shift s in 0..3 makes (u + s - a)/(1 + u) certifiable
    # (only s >= a works: numerator u + (s - a))
    return InequalityFamily(
        name="Wit",
        symbols=(u,),
        grid=GridSpec([("a", [1, 2])]),
        lean_name=lambda pt: f"wit_a{pt['a']}",
        witnesses=lambda pt: [
            (f"shift{s}", (u + s - pt["a"]) / (1 + u)) for s in range(4)
        ],
    )


def test_witness_search_finds_first_certifiable_and_records():
    cf = certify(_wit_fam())
    assert cf.witness_table() == {"wit_a1": "shift1", "wit_a2": "shift2"}
    doc = export_certificates(cf, "a" * 64)
    assert doc["instances"][0]["witness"] == "shift1"


def test_witness_search_exhaustion_refused_with_reasons():
    fam = InequalityFamily(
        name="WitX",
        symbols=(u,),
        grid=GridSpec([("a", [9])]),
        lean_name=lambda pt: "witx",
        witnesses=lambda pt: [(f"s{s}", (u + s - 9) / (1 + u)) for s in range(3)],
    )
    with pytest.raises(CertificationError, match="no certifiable witness"):
        certify(fam)


def test_witness_search_parallel_matches_serial():
    a = certify(_wit_fam()).witness_table()
    b = certify(_wit_fam(), workers=2).witness_table()
    assert a == b


# ---- D: sharpness -----------------------------------------------------------
def test_sharpness_localizes_both_boundaries():
    # target = 1 - cap*u/(1+u): certifiable iff cap <= 1 (num (1+u) - cap*u);
    # claim TRUE iff cap <= 1 too (sup of u/(1+u) is 1) -> boundaries coincide
    def builder(cap):
        return InequalityFamily(
            name="Cap",
            symbols=(u,),
            grid=GridSpec([("i", [0])]),
            lean_name=lambda pt: "cap0",
            target=lambda pt: 1 - cap * u / (1 + u),
        )

    rep = sharpness(builder, sp.Rational(1, 2), sp.Integer(2), steps=5, hunt_iters=200)
    assert rep.cert_lo <= 1 <= rep.cert_hi
    assert rep.truth_witness is not None  # claim genuinely false at cap ~ 2


# ---- E: pilot (workflow-level restriction is tested via restrict_instances) --
def test_pilot_restriction():
    from telperion.certify import restrict_instances

    cf = certify(_wit_fam())
    small = restrict_instances(cf, range(1))
    assert len(small.instances) == 1
    assert small.instances[0].lean_name == "wit_a1"


# ---- F: cilog ---------------------------------------------------------------
def test_cilog_counts_and_classifies():
    log = """\
info: building
error: R3Cert/X.lean:234:82: unsolved goals
⊢ 0 ≤ (2 + u)⁻¹ * 3
error: R3Cert/Y.lean:10:1: unknown identifier 'dispatch_dT00'
warning: something benign
error: R3Cert/Z.lean:5:2: no goals
"""
    diag = parse_log(log)
    assert diag.total_errors == 3
    text = diag.render()
    assert "TOTAL ERRORS: 3" in text
    assert "distributed-spelling" in text     # the ⁻¹ match
    assert "import-DAG" in text
    assert "trailing tactic" in text


# ---- G: per-node potentials -------------------------------------------------
def test_fixed_points_exact():
    m = sp.Symbol("m", nonnegative=True)
    # the origin-shaped step: m' = z/(1 + z*4m) at z = 3/23... use z=1/2, k=1:
    step = sp.Rational(1, 2) / (1 + sp.Rational(1, 2) * m)
    fps = fixed_points(step, m)
    assert len(fps) == 1
    fp = fps[0]
    assert sp.simplify(step.subs(m, fp) - fp) == 0


def test_per_node_family_with_fixed_point_tie():
    # per-node claim: m1*m2 >= 0 with tie at m1=0 (a stand-in per-node shape)
    fam = per_node_family(
        name="PN",
        arity=2,
        per_node_target=lambda ms: ms[0] * ms[1] / (1 + ms[0]),
        ties=lambda pt: [{sp.Symbol("m1", nonnegative=True): sp.Integer(0)}],
    )
    cf = certify(fam)
    assert cf.instances[0].lean_name == "pn_per_node"
    assert cf.checks_passed >= 3  # cert + tie tightness + tie exactness


# ---- H: cone membership -----------------------------------------------------
def test_cone_combination_found_exactly():
    target = 2 * u**2 + 3 * u * v + v**2
    basis = [u**2, u * v, v**2, u]
    cc = cone_combination(target, basis, (u, v))
    assert cc is not None
    assert cc.weights == (2, 3, 1, 0)
    assert sp.simplify(cc.as_expr() - target) == 0


def test_cone_combination_refuses_negative_weight():
    target = u**2 - u * v          # needs lambda = -1 on u*v
    assert cone_combination(target, [u**2, u * v], (u, v)) is None


def test_cone_combination_rational_functions():
    target = (2 * u + 3) / (1 + u)
    basis = [1 / (1 + u), u / (1 + u)]
    cc = cone_combination(target, basis, (u,))
    assert cc is not None
    assert cc.weights == (3, 2)
