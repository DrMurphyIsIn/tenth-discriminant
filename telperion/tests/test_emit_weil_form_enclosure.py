"""Tests for the `weil_form_enclosure` emitter -- the E8 Weil-pairing named-hypothesis seam.

Three layers, in the order the emitter is meant to be trusted:

1. REFUSALS.  Everything the certificate layer must refuse rather than weaken: a
   non-compactly-supported test function (the PNT growth trap), an over-wide box, an inverted
   box, a Hermitian-inconsistent mirror entry, a non-positive lower end for a positivity
   instance, a non-positive worst-case determinant for a Gram block, and the phantom (no boxes).
2. EMISSION.  The emitted Lean states the enclosure as a NAMED HYPOTHESIS and concludes only
   its consequence -- the box literals appear in the hypothesis, the conclusion never asserts
   them, and the proof goes through the abstract `box_pos` / `box_minor_pos` lemmas whose
   numeric side goals are `norm_num`.
3. EVALUATOR.  The Arb backend's own refusals and its rigour invariants (the enclosure brackets
   an independently recomputed value; the anchors run).  Flint-gated so a flint-less checkout
   skips rather than fails.

conjecture1_proved = False.
"""
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import pytest  # noqa: E402
import sympy as sp  # noqa: E402

from telperion.emit_weil_form_enclosure import (  # noqa: E402
    GRAM_MINOR,
    POSITIVITY,
    WeilBox,
    WeilFormEnclosureCert,
    WeilFormEnclosureData,
    WeilFormEnclosureEmitter,
    certify_weil_form_enclosure_point,
    weil_form_enclosure_certificate,
    weil_form_enclosure_family,
    weil_form_prelude_lean,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402
from telperion.negative_control_harness import registered_adapters  # noqa: E402



def _box(i, j, lo, hi, li="g_i", lj="g_j"):
    return WeilBox(i=i, j=j, label_i=li, label_j=lj, lo=sp.Rational(lo), hi=sp.Rational(hi))


def _pos_data(**kw):
    base = dict(
        shape=POSITIVITY,
        boxes=(_box(0, 0, sp.Rational(1, 10), sp.Rational(11, 100)),),
        max_width=sp.Rational(1, 10),
        support_radius=sp.Rational(2),
        arch_T=1024,
        n_byparts=5,
    )
    base.update(kw)
    return WeilFormEnclosureData(**base)


def _gram_data(**kw):
    base = dict(
        shape=GRAM_MINOR,
        boxes=(_box(0, 0, sp.Rational(1, 10), sp.Rational(11, 100)),
               _box(1, 1, sp.Rational(1, 10), sp.Rational(11, 100)),
               _box(0, 1, sp.Rational(1, 100), sp.Rational(2, 100))),
        max_width=sp.Rational(1, 10),
        support_radius=sp.Rational(5, 2),
        arch_T=1024,
        n_byparts=5,
    )
    base.update(kw)
    return WeilFormEnclosureData(**base)


# --- layer 1: refusals -----------------------------------------------------------------

def test_refuses_non_compact_support():
    """The PNT growth trap: for a merely Schwartz g the prime side diverges, so there is no
    pairing to enclose (E8 design memo 2.2)."""
    with pytest.raises(ValueError, match="not compactly supported"):
        weil_form_enclosure_certificate(_pos_data(support_radius=None))
    with pytest.raises(ValueError, match="not compactly supported"):
        weil_form_enclosure_certificate(_pos_data(support_radius=sp.Rational(0)))


def test_refuses_over_wide_box():
    wide = (_box(0, 0, sp.Rational(1, 10), sp.Rational(9, 10)),)
    with pytest.raises(ValueError, match="exceeds the declared threshold"):
        weil_form_enclosure_certificate(_pos_data(boxes=wide))


def test_refuses_inverted_box():
    bad = (_box(0, 0, sp.Rational(11, 100), sp.Rational(1, 10)),)
    with pytest.raises(ValueError, match="inverted box"):
        weil_form_enclosure_certificate(_pos_data(boxes=bad))


def test_refuses_hermitian_inconsistent_mirror():
    """`W_ij` and `W_ji` boxes that do not overlap mean the evaluator disagrees with itself."""
    data = _gram_data(mirror_boxes=(_box(1, 0, sp.Rational(9, 10), sp.Rational(95, 100)),))
    with pytest.raises(ValueError, match="not Hermitian-consistent"):
        weil_form_enclosure_certificate(data)


def test_accepts_hermitian_consistent_mirror():
    data = _gram_data(mirror_boxes=(_box(1, 0, sp.Rational(15, 1000), sp.Rational(25, 1000)),))
    assert weil_form_enclosure_certificate(data).shape == GRAM_MINOR


def test_refuses_non_positive_lower_end():
    bad = (_box(0, 0, sp.Rational(-1, 100), sp.Rational(1, 100)),)
    with pytest.raises(ValueError, match="does not imply 0 < weilForm"):
        weil_form_enclosure_certificate(_pos_data(boxes=bad))


def test_refuses_non_positive_worst_case_determinant():
    """Cauchy-Schwarz violated by the boxes: the block is not certified positive definite."""
    boxes = (_box(0, 0, sp.Rational(1, 10), sp.Rational(11, 100)),
             _box(1, 1, sp.Rational(1, 10), sp.Rational(11, 100)),
             _box(0, 1, sp.Rational(1, 2), sp.Rational(51, 100)))
    with pytest.raises(ValueError, match="margin"):
        weil_form_enclosure_certificate(_gram_data(boxes=boxes, max_width=sp.Rational(1)))


def test_refuses_phantom_and_bad_shapes():
    with pytest.raises(ValueError, match="phantom"):
        weil_form_enclosure_certificate(_pos_data(boxes=()))
    with pytest.raises(ValueError, match="unknown shape"):
        weil_form_enclosure_certificate(_pos_data(shape="nonsense"))
    with pytest.raises(ValueError, match="exactly 3 boxes"):
        weil_form_enclosure_certificate(
            _gram_data(boxes=(_box(0, 0, sp.Rational(1, 10), sp.Rational(11, 100)),)))
    with pytest.raises(ValueError, match="max_width must be"):
        weil_form_enclosure_certificate(_pos_data(max_width=sp.Rational(0)))


def test_margin_is_the_worst_case_determinant():
    cert = weil_form_enclosure_certificate(_gram_data())
    # lo_a * lo_b - max(|c|)^2 = 1/100 - (2/100)^2
    assert cert.margin == sp.Rational(1, 100) - sp.Rational(2, 100) ** 2


# --- layer 2: emission -----------------------------------------------------------------

def _emit_one(data, name):
    fam = weil_form_enclosure_family(
        "T", GridSpec([("k", [0])]), lambda pt: name, spec=lambda pt: data)
    inst, checks = certify_weil_form_enclosure_point(fam, {"k": 0}, name)
    assert checks == 1

    class _F:
        instances = (inst,)
    return WeilFormEnclosureEmitter().emit_body(_F(), LeanProfile())


def test_positivity_emission_is_a_named_hypothesis_seam():
    body, n = _emit_one(_pos_data(), "wf_pos")
    assert n == 1
    # the enclosure is a HYPOTHESIS named henc, not an assertion
    assert ("(henc : ((1 / 10) : ℝ) ≤ (WeilForm.weilForm (WeilForm.crossCorr g g)).re"
            in body)
    assert "0 < (WeilForm.weilForm (WeilForm.crossCorr g g)).re :=" in body
    assert "box_pos henc (by norm_num)" in body
    # the conclusion never restates the literals
    concl = body.split(":=")[0].split(":\n")[-1]
    assert "11 / 100" not in concl
    assert "conjecture1_proved = False" in body
    assert "sorry" not in body


def test_gram_minor_emission_states_both_sylvester_minors():
    body, n = _emit_one(_gram_data(), "wf_gram")
    assert n == 1
    assert "box_minor_pos h00 h11 h01 (by norm_num) (by norm_num) (by norm_num)" in body
    assert "0 < (WeilForm.weilForm (WeilForm.crossCorr g0 g0)).re ∧" in body
    assert "- (WeilForm.weilForm (WeilForm.crossCorr g0 g1)).re ^ 2" in body
    assert "sorry" not in body


def test_prelude_carries_the_falsifiability_face_with_an_undischarged_hypothesis():
    pre = weil_form_prelude_lean()
    assert "theorem weil_negative_refutes_rh" in pre
    # the RH content is a HYPOTHESIS, never proved here
    assert "hpos : RiemannHypothesis → 0 ≤" in pre
    assert "¬ RiemannHypothesis" in pre
    assert "sorry" not in pre
    assert "theorem box_pos" in pre and "theorem box_minor_pos" in pre


def test_emitted_lean_carries_no_emoji():
    body, _ = _emit_one(_gram_data(), "wf_gram")
    text = body + weil_form_prelude_lean()
    assert all(ord(ch) < 0x2190 or ch in "≤≥∧∨¬→ℝℂℕ∞⊤⟨⟩←↑↓∫∑′·√ρψγΓΛπ" for ch in text), \
        "house rule: no emoji in emitted code"


# --- layer 3: the Arb evaluator ---------------------------------------------------------

def test_evaluator_refuses_non_compact_spec():
    pytest.importorskip("flint")
    from telperion.weil_form_eval import (
        GaussianSpec, WeilTestSpec, enclose_weil_form_entry)
    g = GaussianSpec("gauss", a=Fraction(1, 5))
    with pytest.raises(ValueError, match="not compactly supported"):
        enclose_weil_form_entry(g, WeilTestSpec("bump"))
    with pytest.raises(ValueError, match="n_byparts"):
        enclose_weil_form_entry(WeilTestSpec("bump"), WeilTestSpec("bump"), n_byparts=1)


def test_evaluator_spec_rejects_degenerate_width():
    from telperion.weil_form_eval import WeilTestSpec
    with pytest.raises(ValueError, match="width must be"):
        WeilTestSpec("bad", width=Fraction(0))


def test_evaluator_anchors_run():
    pytest.importorskip("flint")
    from telperion.weil_form_eval import self_check
    self_check()   # raises if a normalisation/index anchor is off


def test_round_outward_only_widens():
    from telperion.weil_form_eval import round_outward
    lo, hi = Fraction("0.0001239578185126834"), Fraction("0.00012689612861283578")
    rlo, rhi = round_outward(lo, hi)
    assert rlo <= lo and rhi >= hi
    nlo, nhi = round_outward(Fraction(-7, 3), Fraction(-1, 3))
    assert nlo <= Fraction(-7, 3) and nhi >= Fraction(-1, 3)


def test_enclosure_brackets_an_independent_recomputation():
    """The box at one precision must contain the box computed at a higher precision -- the
    evaluator's own rigour invariant (a radius bug shows up as disjoint boxes)."""
    pytest.importorskip("flint")
    from telperion.weil_form_eval import WeilTestSpec, enclose_weil_form_entry
    s = WeilTestSpec("bump_w1", width=Fraction(1))
    a = enclose_weil_form_entry(s, s, prec_bits=56, arch_T=32, n_byparts=5)
    b = enclose_weil_form_entry(s, s, prec_bits=90, arch_T=32, n_byparts=5)
    assert not (a.hi < b.lo or b.hi < a.lo), f"disjoint boxes {a.lo, a.hi} vs {b.lo, b.hi}"
    assert a.lo > 0 or a.hi > 0


# --- the negative control is declared and wired ------------------------------------------

def test_negative_control_adapter_is_registered_and_forges_a_false_instance():
    ad = registered_adapters()["WeilFormEnclosureEmitter"]
    false_cert = ad.make_false_cert()
    # Layer 1 would have refused the forgery -- that is the point of hand-minting it.
    data = WeilFormEnclosureData(
        shape=false_cert.shape, boxes=false_cert.boxes, max_width=sp.Rational(1),
        support_radius=false_cert.support_radius)
    with pytest.raises(ValueError, match="margin"):
        weil_form_enclosure_certificate(data)
    # ... and the true twin is genuinely certifiable.
    true_cert = ad.make_true_cert()
    ok = WeilFormEnclosureData(
        shape=true_cert.shape, boxes=true_cert.boxes, max_width=true_cert.max_width,
        support_radius=true_cert.support_radius)
    assert weil_form_enclosure_certificate(ok).margin > 0
    assert isinstance(true_cert, WeilFormEnclosureCert)
