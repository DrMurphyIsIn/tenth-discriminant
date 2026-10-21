"""The Dedekind product-closure control for clause (B-mult-twisted).

zeta_K for K = Q(sqrt(-5)) (D = -20, h = 2) is zeta(s) * L(s, chi_{-20}).  Both factors
PASS the multiplicativity clause; their product FAILS it.  These tests need no libflint
(they never load the certified zeta ladder), so they run in the required `unit` job.

conjecture1_proved = False.
"""
import sys
from pathlib import Path

import pytest

_QC = Path(__file__).resolve().parent.parent / "examples" / "quasicrystal"
sys.path.insert(0, str(_QC))

zoo = pytest.importorskip("zoo")


# --- the Kronecker symbol, against a hand table --------------------------------
# (-20 / p) = +1 iff p = 1, 3, 7, 9 (mod 20); -1 iff p = 11, 13, 17, 19 (mod 20).
@pytest.mark.parametrize("p,val", [
    (3, 1), (7, 1), (23, 1), (29, 1), (41, 1), (43, 1), (47, 1), (61, 1), (67, 1), (83, 1),
    (11, -1), (13, -1), (17, -1), (19, -1), (31, -1), (37, -1), (53, -1), (59, -1), (71, -1),
    (2, 0), (5, 0),
])
def test_kronecker_m20_at_primes(p, val):
    assert zoo._kronecker(-20, p) == val


def test_kronecker_is_completely_multiplicative_in_n():
    for m in range(1, 60):
        for n in range(1, 60):
            assert zoo._kronecker(-20, m * n) == zoo._kronecker(-20, m) * zoo._kronecker(-20, n)


# --- the anti-phantom face: ideal counts vs representation numbers --------------
def test_ideal_counts_match_form_representations():
    a = zoo._dedekind_coeffs(-20, 80)
    for n in range(1, 81):
        assert zoo._form_reps_m20(n) == 2 * a[n], n


def test_ideal_counts_first_values():
    # #ideals of norm n in Z[sqrt(-5)], n = 1..12: 1,1,2,1,1,2,2,1,3,1,0,2
    a = zoo._dedekind_coeffs(-20, 12)
    assert a[1:] == [1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 0, 2]


def test_loader_refuses_on_a_corrupted_coefficient(monkeypatch):
    real = zoo._dedekind_coeffs

    def corrupt(D, N):
        a = real(D, N)
        a[6] += 1          # a phantom ideal of norm 6
        return a
    monkeypatch.setattr(zoo, "_dedekind_coeffs", corrupt)
    with pytest.raises(RuntimeError, match="REFUSED"):
        zoo._load_dedekind()


# --- the verdicts ---------------------------------------------------------------
def test_factor_L_chi_m20_passes_bmult_twisted():
    v, d = zoo.check_multiplicativity(zoo._load_l_chim20())
    assert v == zoo.PASS
    assert "UNIMODULAR" in d and "ramified primes" in d and "[2, 5]" in d


def test_dedekind_fails_bmult_twisted_at_the_first_split_prime():
    v, d = zoo.check_multiplicativity(zoo._load_dedekind())
    assert v == zoo.FAIL
    assert "|t(3)|=2.0000" in d          # b(3) = 2 log 3: the degree-2 layer, not a twist


def test_dedekind_fails_bare_positivity_for_missing_atoms_not_sign():
    v, d = zoo.check_weight_positivity(zoo._load_dedekind())
    assert v == zoo.FAIL
    assert "inert" in d and ">= 0" in d


def test_dedekind_is_conditional_where_zeta_is():
    obj = zoo._load_dedekind()
    assert zoo.check_atomic_spectrum_loglattice(obj)[0] == zoo.COND
    assert zoo.check_defect_bounded(obj)[0] == zoo.COND
    assert zoo.check_temperedness(obj)[0] == zoo.PASS
    assert zoo.check_support_density(obj)[0] == zoo.PASS


def test_product_layer_is_sum_of_factor_layers():
    """The log-derivative of zeta_K is the SUM of the log-derivatives of the factors:
    b_K(p^m) = (log p)(1 + chi(p)^m).  Check the recursion agrees with the closed form."""
    import math
    a = zoo._dedekind_coeffs(-20, 60)
    b = zoo._von_mangoldt_analogue([0j] + [complex(x) for x in a[1:]], 60)
    for p, chi in [(3, 1), (7, 1), (11, -1), (13, -1), (2, 0), (5, 0)]:
        pk, m = p, 1
        while pk <= 60:
            want = math.log(p) * (1 + chi ** m)
            assert abs(b[pk] - want) < 1e-9, (p, m, b[pk], want)
            pk *= p
            m += 1
    for n in (6, 10, 12, 14, 15, 21, 22, 30):
        assert abs(b[n]) < 1e-9, n          # no composite atoms: it IS an Euler product


def test_forged_twin_dropping_the_L_factor_flips_to_pass():
    genuine, _ = zoo.check_multiplicativity(zoo._load_dedekind())
    forged = zoo.ZooObject(name="forged", kind="l_function", spectrum="prime_log_lattice",
                           weights="nonneg_ideal", density_count=50, density_model=50.0,
                           t_max=100.0, mult_model="dedekind_quadratic",
                           mult_coeffs=("dedekind", [0j] + [1 + 0j] * 60))
    assert genuine == zoo.FAIL
    assert zoo.check_multiplicativity(forged)[0] == zoo.PASS


def test_dedekind_governance_block_without_libflint():
    """Run the DEDEKIND block of run_asserts on a matrix built from the flint-free
    members plus a descriptor-only zeta row (the certified ladder is not needed for
    any Dedekind assertion)."""
    objs = [zoo.ZooObject(name="zeta", kind="zeta", spectrum="prime_log_lattice",
                          weights="positive_prime", density_count=29, density_model=28.1,
                          t_max=100.0, mult_model="euler_product", mult_coeffs=("cm", {})),
            zoo._load_dh(), zoo._load_l_chi5(), zoo._load_delta(),
            zoo._load_l_chim20(), zoo._load_dedekind(),
            zoo._load_lattice(), zoo._load_ksly(), zoo._load_random()]
    matrix = {o.name: {k: {"verdict": c(o)[0], "detail": c(o)[1], "variants": vs, "name": h}
                       for k, h, vs, c in zoo.CLAUSES} for o in objs}
    vk = {}
    for variant in ("A", "B", "Bm", "C", "D"):
        vk[variant] = {}
        for o in objs:
            cl = [k for k, _, vs, _ in zoo.CLAUSES if variant in vs]
            fails = [k for k in cl if matrix[o.name][k]["verdict"] == zoo.FAIL]
            vk[variant][o.name] = {
                "fails": fails, "killed": bool(fails),
                "survives": all(matrix[o.name][k]["verdict"] in (zoo.PASS, zoo.COND, zoo.NA)
                                for k in cl)}
    res = {"matrix": matrix, "variant_kill": vk, "forged_controls": [],
           "objects": [o.name for o in objs],
           "object_meta": {o.name: {"density_count": o.density_count, "offline_pairs": 0,
                                    "spectrum": o.spectrum, "weights": o.weights} for o in objs}}
    findings, failures = zoo.run_asserts(res)
    assert [f for f in failures if "DEDEKIND" in f] == []
    assert any(f.startswith("DEDEKIND CONTROL CONFIRMED") for f in findings)
    assert vk["Bm"]["dedekind_m20"]["killed"]
    assert vk["Bm"]["l_chim20"]["survives"]
    for variant in ("A", "C", "D"):
        assert vk[variant]["dedekind_m20"]["survives"]
