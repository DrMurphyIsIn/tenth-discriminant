"""Physics-transfer probes for BG: SUSY (Witten) index, determinantal kernel, Dirac index.

Unified finding these tests pin: each supplies a non-separable, deformation-invariant INTEGER of the right
shape (cannot overshoot), but NONE localizes the tie -- because the tie is an ARITHMETIC (23-adic) resonance
of the (64/621)^n weight, external to any geometric/spectral object. Only the 23-adic carrier localizes it.
conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    DeterminantalKernelProbe,
    DiracIndexProbe,
    SusyIndexProbe,
    dirac_chiral_index,
    girardeau_determinant,
    near_star_determinant_closed_form,
    signed_matching_index,
)
from telperion.bg.frustration_free import near_star_edges  # noqa: E402
from telperion.bg.susy_index import adjacency_nullity  # noqa: E402


# --- #1 SUSY / Witten index ---
def test_susy_indices_constant_on_near_stars():
    for s in (2, 3, 4, 5, 6):
        n, e = near_star_edges(s)
        assert signed_matching_index(n, e) == 0        # Euler char of matching complex
        assert adjacency_nullity(n, e) == 1            # fermion zero modes


def test_susy_probe_check_and_bps_framing():
    probe = SusyIndexProbe()
    assert probe.check()
    assert probe.tie_is_bps_zero_energy()
    assert not probe.indices_integer_and_deformation_invariant() is False  # they ARE
    assert "BPS" in probe.finding() or "zero-energy" in probe.finding()


# --- #3 determinantal kernel ---
def test_girardeau_determinant_closed_form():
    for s in (2, 3, 4, 5, 6):
        n, e = near_star_edges(s)
        assert girardeau_determinant(n, e) == near_star_determinant_closed_form(s)
    assert near_star_determinant_closed_form(5) == Fr(81, 8)   # tie value, unremarkable in the sequence


def test_determinantal_probe_check_generic_spectrum():
    probe = DeterminantalKernelProbe()
    assert probe.check()
    assert probe.spectrum_generic_across_near_stars()
    assert probe.determinant_does_not_localize_tie()


# --- #2 Dirac index ---
def test_dirac_index_equals_nullity_and_constant():
    for s in (2, 3, 4, 5, 6):
        n, e = near_star_edges(s)
        assert dirac_chiral_index(n, e) == adjacency_nullity(n, e) == 1


def test_dirac_probe_gate_is_23adic_not_dirac():
    probe = DiracIndexProbe()
    assert probe.check()
    assert probe.gate_is_23adic_not_dirac()
    f = probe.finding()
    assert "23-adic" in f and "conjecture1_proved = False" in f
