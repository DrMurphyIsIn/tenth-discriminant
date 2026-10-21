"""Tests for the composed BG asymptotic-upper-bound reduction skeleton (`telperion.bg_upper_bound`).

Verifies the honest ledger: every GATED step's certificate `.check()`s; exactly one HYPOTHESIS (the small-degree
refined ceiling (b)) remains open; `conjecture_proved` is `False`.  conjecture1_proved = False.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg_upper_bound import (  # noqa: E402
    GATED, HYPOTHESIS, UpperBoundReduction, conjecture1_proved,
)


def test_all_gated_steps_check():
    """Every GATED step of the reduction carries a certificate that checks exactly (the kernel-gated pieces:
    slack, mixed-KKT brooms, high-degree tail, broom optimum)."""
    R = UpperBoundReduction.build()
    gated = R.verify_gated()
    # slack, mixed-KKT, high-deg tail, M_d finite, near-broom unimodal, extremality price-map, broom-vs-cherry (#4),
    # leaf-exchange (#5), SCL-assembly-consistency, broom opt
    assert len(gated) == 10
    assert all(gated.values()), gated
    assert R.gated_ok()


def test_exactly_one_open_hypothesis():
    """The reduction has EXACTLY one open analytic input.  After the 2026-09-02 extremality assembly, all its
    arithmetic legs (price-map, broom-vs-cherry #4, leaf-exchange #5, hi-degree, near-broom, assembly-consistency)
    are GATED, so the sole HYPOTHESIS is now the well-founded SCL RECURSION on |c| (the Lean induction glue)."""
    R = UpperBoundReduction.build()
    opens = R.open_hypotheses()
    assert len(opens) == 1
    assert opens[0].kind == HYPOTHESIS
    assert opens[0].tag == "2b-lo-scl-induction"
    assert "argmax" in opens[0].statement


def test_conjecture_not_proved():
    """The composed reduction does NOT claim the conjecture: an open HYPOTHESIS remains, so
    `conjecture_proved` is False (and the module flag stays False)."""
    R = UpperBoundReduction.build()
    assert R.conjecture_proved is False
    assert conjecture1_proved is False


def test_step_kinds_are_wellformed():
    """Every step has a recognized kind, and GATED steps carry a certificate factory while non-GATED do not."""
    R = UpperBoundReduction.build()
    assert len(R.steps) == 14
    for s in R.steps:
        assert s.kind in {"GATED", "BASE", "BOUNDARY", "LEMMA", "HYPOTHESIS"}
        if s.kind == GATED:
            assert s.cert is not None and s.verify() is True
        else:
            assert s.verify() is None
