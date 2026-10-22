"""The BraggDefect ``hexp`` seam discharged by the scaled_interval_eval emitter.

``examples/bragg_defect_sie/generate.py`` emits ``BraggDefectSIE.lean`` and a copy of the
``ScaledInterval`` prelude INTO the zeta_zero_localization island; ``BraggDefect.lean`` (driver
``bragg_defect.py``) states ``defect_witness_offline_sie`` and friends with no ``hexp`` binder.

Pure-Python checks: the drift gate, the prelude copy is byte-identical to the emitter's single
source (and to the scaled_interval_eval island's copy), the claims are read from the island, and
Layer 1 refuses a claim one ulp inside the computed box.

Lean-gated (zzl_aux env built): the two-sided negative control on the REAL Bragg instance, via the
same harness the emitter's registered adapter uses (prelude spliced, Mathlib only).  The FALSE twin
is the honest certificate with the root box's upper end shrunk by one ulp, and separately with the
claimed upper bound moved one ulp below the computed box; the kernel rejects both, and the honest
twin compiles axiom-clean.

conjecture1_proved = False.
"""
from __future__ import annotations

import importlib.util
import sys
from dataclasses import replace
from pathlib import Path

import pytest
import sympy as sp

_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(_ROOT / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from telperion.emit_scaled_interval_eval import (  # noqa: E402
    ScaledIntervalEvalEmitter,
    scaled_interval_eval_certificate,
    scaled_interval_prelude_body,
    scaled_interval_prelude_lean,
)

_GEN = _ROOT / "examples" / "bragg_defect_sie" / "generate.py"
_ISLAND = _ROOT / "examples" / "zeta_zero_localization" / "lean"
_AUX = _ISLAND / "zzl_aux"


@pytest.fixture(scope="module")
def gen():
    spec = importlib.util.spec_from_file_location("bragg_defect_sie_generate", _GEN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _cert(gen, case: int):
    spec = dict(gen.specs()[case][1])
    return scaled_interval_eval_certificate(spec.pop("expr"), **spec)


# --- pure Python -------------------------------------------------------------------------

def test_check_mode_is_clean(gen):
    assert gen.main(check=True) == 0


def test_prelude_copy_is_the_single_source():
    island = (_ISLAND / "ScaledInterval.lean").read_text(encoding="utf-8")
    sibling = (_ROOT / "examples" / "scaled_interval_eval" / "lean"
               / "ScaledInterval.lean").read_text(encoding="utf-8")
    assert island == scaled_interval_prelude_lean() == sibling


def test_claims_are_the_island_constants(gen):
    lo, hi = gen.island_offline_bracket()
    assert lo < hi < 0
    elo, ehi = gen.island_exp_bracket()
    assert elo == sp.Rational(442068367230259049924676660787771898883,
                              400000000000000000000000000000000000000)
    assert ehi == sp.Rational(11051709180756476248117094953514706601127, 10 ** 40)
    off = _cert(gen, 0)
    assert (off.claim_lo, off.claim_hi) == (lo, hi)
    assert off.scale == 10 ** 40
    assert sum(nd.op == "exp" for nd in off.nodes) == 2


def test_bridge_theorems_are_stated_without_hexp():
    src = (_ISLAND / "BraggDefect.lean").read_text(encoding="utf-8")
    for name in ("hexp_sie", "defect_witness_offline_sie", "bragg_defect_witness_sie",
                 "defect_leakage_gap_sie"):
        start = src.index(f"theorem {name} :")
        stmt = src[start:src.index(":=", start)]
        assert "(hexp" not in stmt, name
    # the hexp-taking originals are still there, unchanged in shape
    for name in ("defect_witness_offline", "bragg_defect_witness", "defect_leakage_gap"):
        assert f"theorem {name}\n    (hexp : expLo ≤ Real.exp (1 / 10) ∧" in src, name
    for bad in ("sorry", "native_decide", "\naxiom "):
        assert bad not in src
        assert bad not in (_ISLAND / "BraggDefectSIE.lean").read_text(encoding="utf-8")


def test_layer1_refuses_a_claim_one_ulp_inside_the_box(gen):
    off = _cert(gen, 0)
    lo, hi = off.nodes[off.root].box
    spec = dict(gen.specs()[0][1])
    expr = spec.pop("expr")
    with pytest.raises(ValueError, match="REFUSED"):
        scaled_interval_eval_certificate(expr, scale=off.scale, lo=off.claim_lo,
                                         hi=sp.Rational(hi - 1, off.scale))
    with pytest.raises(ValueError, match="REFUSED"):
        scaled_interval_eval_certificate(expr, scale=off.scale, hi=off.claim_hi,
                                         lo=sp.Rational(lo + 1, off.scale))


# --- Lean (gated on the zzl_aux env) -----------------------------------------------------

def _env_ready() -> bool:
    from lean_env import lean_env_ready
    olean = _AUX / ".lake" / "build" / "lib" / "lean" / "ScaledInterval.olean"
    return lean_env_ready(_AUX) and olean.is_file()


lean = pytest.mark.skipif(not _env_ready(), reason="zzl_aux Lean env not built -- skipped")


def _emit(cert, name: str) -> str:
    from telperion.negative_control_harness import emit_via_single_instance_family
    return emit_via_single_instance_family(
        ScaledIntervalEvalEmitter(), lean_name=name, instance_kwargs={"payload": cert})


def _adapter(make_false, make_true, label):
    from telperion.negative_control_harness import NegativeControlAdapter
    return NegativeControlAdapter(
        emitter_name="ScaledIntervalEvalEmitter", make_false_cert=make_false,
        make_true_cert=make_true, emit_call=_emit, prelude=scaled_interval_prelude_body(),
        label=label, imports_line="import Mathlib")


@lean
def test_lean_negative_control_root_box_one_ulp(gen):
    from telperion.negative_control_harness import generic_negative_control

    def false_cert():
        c = _cert(gen, 0)
        nodes = list(c.nodes)
        r = nodes[c.root]
        nodes[c.root] = replace(r, box=(r.box[0], r.box[1] - 1))
        return replace(c, nodes=tuple(nodes))

    res = generic_negative_control(
        _adapter(false_cert, lambda: _cert(gen, 0),
                 "Bragg off-line defect root box shrunk by one ulp"),
        env_dir=str(_AUX), false_name="bragg_sie_forged_box", true_name="bragg_sie_true")
    assert res.kernel_rejects and res.true_compiles and res.okay, res.detail


@lean
def test_lean_negative_control_claim_one_ulp(gen):
    from telperion.negative_control_harness import generic_negative_control

    def false_cert():
        c = _cert(gen, 0)
        hi = c.nodes[c.root].box[1]
        return replace(c, claim_hi=sp.Rational(hi - 1, c.scale))

    res = generic_negative_control(
        _adapter(false_cert, lambda: _cert(gen, 0),
                 "Bragg off-line defect claim upper end one ulp below the computed box"),
        env_dir=str(_AUX), false_name="bragg_sie_forged_claim", true_name="bragg_sie_true2")
    assert res.kernel_rejects and res.true_compiles and res.okay, res.detail
