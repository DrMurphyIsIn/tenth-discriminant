"""Uniform-in-recursion monotone-tail (arm-dominance) tests."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.bg import ArmDominanceCertificate, arm_dominance_uniform  # noqa: E402

def test_arm_dominance_at_tie():
    assert ArmDominanceCertificate("t", 0, 5).check()

def test_arm_dominance_NOT_uniform_tie_beats_arm():
    # SCOPE CORRECTION: with the tie in the candidate set and k past 19, arm-dominance
    # FAILS -- the 11-node tie N(0,5) beats the arm for all k >= 19 (marginal-tie wall).
    holds, exc = arm_dominance_uniform(range(0,1), range(0,26))
    assert not holds and (0,0) in exc and (0,19) in exc

def test_arm_dominance_across_cherries():
    for cr in range(0,4):
        for k in range(1,6):
            assert ArmDominanceCertificate("t", cr, k).check()

def test_lean_emits_cross_multiplied():
    lean = ArmDominanceCertificate("t", 0, 5).lean()
    assert "norm_num" in lean and "≤" in lean and "ARM-DOMINANCE" in lean
