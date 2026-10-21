"""The F <= h(mu) envelope: mapped and shown non-inductive.

Pins: the empirical envelope peaks at exactly 1 at the tie, is < 1 elsewhere, the tie's children are the
extremizers -- AND the envelope is not a supersolution, so no single-variable h(mu) closes the induction.
A reasoned dead-end, not a proof. conjecture1_proved = False.
"""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import EnvelopeCertificate  # noqa: E402
from telperion.bg.envelope import _collect_vertices, empirical_envelope  # noqa: E402
from telperion.bg.frustration_free import near_star_edges  # noqa: E402
from telperion.bg.recursive_transfer import W  # noqa: E402


def test_envelope_peaks_at_the_tie():
    cert = EnvelopeCertificate(m_max=9)
    assert cert.envelope_peaks_at_tie()          # max h* = 1 at mu = 3/23
    assert cert.envelope_below_one()             # h* <= 1, equality only at the tie


def test_tie_children_are_the_extremizers():
    n, e = near_star_edges(5)
    verts = _collect_vertices(9, extra_blocks=[(n, e, 0)])
    env = empirical_envelope(verts)
    assert env[Fr(1)] == W                        # leaf is the unique block at mu = 1
    assert env[Fr(1, 3)] == Fr(486, 529)          # arm/mid is the max at mu = 1/3
    assert env[Fr(3, 23)] == 1                     # tie hub


def test_mu_envelope_is_not_a_supersolution():
    cert = EnvelopeCertificate(m_max=9)
    viol, total, worst = cert.mu_envelope_not_inductive()
    assert total > 0
    assert viol > 0                               # the step (64/621)a^11 prod h*(mu_c) <= h*(mu_v) FAILS
    assert worst > 1                              # overshoots the TIGHT envelope h* (a larger h can close)


def test_certificate_check_and_scope():
    cert = EnvelopeCertificate(m_max=9)
    assert cert.check()
    f = cert.finding()
    assert "TIGHT envelope is not a supersolution" in f
    assert "does NOT rule out single-variable envelopes" in f
    assert "conjecture1_proved = False" in f
