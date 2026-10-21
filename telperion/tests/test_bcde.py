"""Avenues B (zero-free), C (entropy/Bregman), D (Ehrhart), E (graph-limit) tests."""
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.bg import (  # noqa: E402
    BregmanCertificate,
    ZeroFreeDiskCertificate,
    bregman_bound,
    dominant_term_margin,
    free_energy_density,
    is_quasi_polynomial,
    matching_polynomial,
    minimal_period,
    permanent01,
)


# --- B: zero-free region ---------------------------------------------------
def test_zerofree_dominant_term():
    assert dominant_term_margin([Fr(10), Fr(1), Fr(1)], Fr(2)) > 0     # zero-free in |z|<=2
    assert dominant_term_margin([Fr(1), Fr(1), Fr(1)], Fr(2)) < 0      # not (a0 too small)
    assert ZeroFreeDiskCertificate("t", (10, 1, 1), Fr(2)).check()


# --- C: entropy / Bregman --------------------------------------------------
def test_bregman_bound_holds():
    A = ((1, 1, 0), (1, 1, 1), (0, 1, 1))
    assert permanent01(A) == 3
    assert permanent01(A) <= bregman_bound(A)
    assert BregmanCertificate("t", A).check()                          # cleared integer form


def test_permanent_identity():
    A = ((1, 1), (1, 1))
    assert permanent01(A) == 2                                          # perm[[1,1],[1,1]]=2


# --- D: Ehrhart quasi-polynomial ------------------------------------------
def test_quasi_polynomial_period():
    # 0,1,0,1,... is quasi-polynomial of period 2 (constant on each residue)
    seq = [i % 2 for i in range(12)]
    assert is_quasi_polynomial(seq, 2)
    assert not is_quasi_polynomial(seq, 1)                             # not a single polynomial
    assert minimal_period(seq, [1, 2, 3]) == 2


def test_polynomial_is_period_one():
    seq = [i * i for i in range(8)]                                    # n^2: period 1
    assert is_quasi_polynomial(seq, 1)
    assert minimal_period(seq, [1, 2, 3]) == 1


# --- E: graph limit / matching measure ------------------------------------
def test_matching_polynomial_star():
    # S_4 (star, 4 leaves): 1 empty + 4 single-edge + 0 two-edge matchings
    assert matching_polynomial({0: {1, 2, 3, 4}, 1: {0}, 2: {0}, 3: {0}, 4: {0}}) == [1, 4, 0]


def test_matching_polynomial_path():
    # P4 (path a-b-c-d): matchings {}, {ab},{bc},{cd}, {ab,cd} -> [1,3,1]
    adj = {0: {1}, 1: {0, 2}, 2: {1, 3}, 3: {2}}
    assert matching_polynomial(adj) == [1, 3, 1]


def test_free_energy_density_positive():
    assert free_energy_density({0: {1}, 1: {0}}) > 0
