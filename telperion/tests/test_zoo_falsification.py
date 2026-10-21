"""Required-outcome tests for the MIRRORMERE falsification harness (QC-B1).

These assert the §8 governance matrix outcomes from QC_AXIOMS_DRAFT.md: DH (the
off-line-zero control) must die on every LIVE variant (A/B/D) on its predicted
clause and SURVIVE the dead control C; zeta's certified data passes unconditional
clauses and is CONDITIONAL on RH-clauses; the positive controls (lattice, ksly)
survive; random is killed; and every forged-input negative control flips.

conjecture1_proved = False.
"""
import sys
from pathlib import Path

import pytest

_QC = Path(__file__).resolve().parent.parent / "examples" / "quasicrystal"
sys.path.insert(0, str(_QC))

try:
    import zoo  # noqa: E402
    _HAVE = zoo._load_zeta is not None
except Exception:  # pragma: no cover
    _HAVE = False

try:
    from telperion.arb_platt import PLATT_AVAILABLE as _PLATT
except Exception:  # pragma: no cover - import failure counts as unavailable
    _PLATT = False

pytestmark = [
    pytest.mark.skipif(not _HAVE, reason="quasicrystal zoo harness unavailable"),
    pytest.mark.skipif(not _PLATT, reason="libflint with Platt machinery not found"),
]


@pytest.fixture(scope="module")
def result():
    r = zoo.build_matrix(100.0)
    r["forged_controls"] = zoo.forged_controls()
    return r


def test_no_governance_failures(result):
    findings, failures = zoo.run_asserts(result)
    assert failures == [], f"governance rails broken: {failures}"


def test_dh_dies_on_every_live_variant(result):
    vk = result["variant_kill"]
    for variant in ("A", "B", "D"):
        assert vk[variant]["dh"]["killed"], f"DH must be killed by live variant {variant}"


def test_dh_killed_on_predicted_clause(result):
    m = result["matrix"]["dh"]
    assert m["weight_positivity"]["verdict"] == zoo.FAIL      # B killer = positivity
    assert m["defect_bounded"]["verdict"] == zoo.FAIL         # D killer = unbounded defect
    assert m["atomic_spectrum"]["verdict"] == zoo.FAIL        # A sep = prime log-lattice


def test_dh_survives_dead_control_C(result):
    vk = result["variant_kill"]
    assert vk["C"]["dh"]["survives"] and not vk["C"]["dh"]["killed"]


def test_positivity_is_the_isolated_killer(result):
    """C(pass)/B(fail) differ only by positivity => DH kill attributable to positivity."""
    m = result["matrix"]["dh"]
    assert m["signed_decay"]["verdict"] in (zoo.PASS, zoo.COND)   # C passes
    assert m["weight_positivity"]["verdict"] == zoo.FAIL          # B fails


def test_zeta_conditional_labels(result):
    m = result["matrix"]["zeta"]
    assert m["support_density"]["verdict"] == zoo.PASS
    assert m["weight_positivity"]["verdict"] == zoo.PASS          # unconditional arithmetic
    assert m["atomic_spectrum"]["verdict"] == zoo.COND            # RH-conditional, never PASS
    assert m["defect_bounded"]["verdict"] == zoo.COND             # k=0 <=> RH


def test_positive_controls_survive(result):
    vk = result["variant_kill"]
    assert vk["B"]["lattice"]["survives"]
    assert vk["B"]["ksly"]["survives"]


def test_random_is_killed(result):
    assert result["matrix"]["random"]["atomic_spectrum"]["verdict"] == zoo.FAIL
    assert result["variant_kill"]["B"]["random"]["killed"]


def test_all_forged_controls_flip(result):
    for fc in result["forged_controls"]:
        assert fc["flipped"], (
            f"forged control {fc['control']} on {fc['clause']} did not flip "
            f"(genuine={fc['genuine']} forged={fc['forged_verdict']})")


def test_dh_fails_bmult_multiplicativity(result):
    """W3a: DH FAILS the B-mult multiplicativity clause -- no Euler product means the
    log-derivative has a nonzero amplitude at the COMPOSITE frequency log 6."""
    m = result["matrix"]["dh"]
    assert m["multiplicativity"]["verdict"] == zoo.FAIL
    assert "COMPOSITE" in m["multiplicativity"]["detail"]
    assert result["variant_kill"]["Bm"]["dh"]["killed"]


def test_zeta_passes_bmult_generation_unconditionally(result):
    """W3a: the multiplicative GENERATION of zeta's amplitudes is unconditional/
    arithmetic (PASS), while pure-pointness of the dual comb stays RH-conditional."""
    m = result["matrix"]["zeta"]
    assert m["multiplicativity"]["verdict"] == zoo.PASS
    assert m["atomic_spectrum"]["verdict"] == zoo.COND   # RH clause unchanged by B-mult
    assert result["variant_kill"]["Bm"]["zeta"]["survives"]


def test_bmult_strictly_sharper_than_b(result):
    """W3a: B-mult excludes generic Lee-Yang FQs that B admitted.  ksly survives B
    (positive-mass FQ) but is killed by B-mult (amplitudes not multiplicatively
    generated) -- the axiom carves out the arithmetic FQs.  This is the FEATURE."""
    vk = result["variant_kill"]
    assert vk["B"]["ksly"]["survives"]
    assert vk["Bm"]["ksly"]["killed"]
    assert result["matrix"]["ksly"]["multiplicativity"]["verdict"] == zoo.FAIL
    assert result["matrix"]["random"]["multiplicativity"]["verdict"] == zoo.FAIL


def test_multiplicativity_implies_positivity(result):
    """W3a/W3c TWIST-AWARE dominance.  The relation between B-mult-twisted and bare
    (B-iii) positivity depends on the twist:
      * TRIVIAL twist (zeta): B-mult => positivity (t(p)=+1 => real positive layer).
      * UNIMODULAR-COMPLEX twist (L(chi)): B-mult-twisted holds but bare positivity
        legitimately FAILS -- this is the W3c discovery (bare positivity is
        zeta-unique / over-sharp), NOT a dominance violation.
    So: trivial-twist objects passing B-mult must pass positivity; twisted ones need
    not (and, being genuinely complex, must not)."""
    m = result["matrix"]
    for name in result["objects"]:
        if m[name]["multiplicativity"]["verdict"] != zoo.PASS:
            continue
        detail = m[name]["multiplicativity"]["detail"]
        twisted = ("UNIMODULAR" in detail) or ("chi(p)" in detail)
        pos = m[name]["weight_positivity"]["verdict"]
        if not twisted:
            assert pos in (zoo.PASS, zoo.COND), (
                f"{name} passes B-mult (trivial twist) but not positivity")
        else:
            assert pos == zoo.FAIL, (
                f"{name} passes B-mult-TWISTED (complex) but ALSO passes bare "
                f"positivity -- the over-sharpness claim would be wrong")


def test_broken_multiplicativity_forged_control_flips(result):
    """W3a forged negative control: corrupting a single amplitude (a(6)!=a(2)a(3))
    injects a composite atom -> generation FAILS -> verdict flips PASS->FAIL."""
    fc = next(c for c in result["forged_controls"]
              if c["control"] == "broken_multiplicativity")
    assert fc["flipped"]
    assert fc["genuine"] == zoo.PASS and fc["forged_verdict"] == zoo.FAIL


def test_l_function_passes_bmult_twisted(result):
    """W3c L-COLUMN (the decisive falsification test): a genuine Dirichlet L-function
    L(chi) -- an Euler product with a UNIMODULAR character twist -- PASSES the
    B-mult-twisted clause, and does so via the TWISTED (character) reading, not the
    trivial-twist zeta reading."""
    m = result["matrix"]["l_chi5"]
    assert m["multiplicativity"]["verdict"] == zoo.PASS
    detail = m["multiplicativity"]["detail"]
    assert "UNIMODULAR" in detail or "chi(p)" in detail
    assert result["variant_kill"]["Bm"]["l_chi5"]["survives"]


def test_l_function_fails_bare_positivity_oversharp(result):
    """W3c: L(chi)'s prime layer is (log p) chi(p)^m p^{-m/2} -- UNIMODULAR COMPLEX,
    not strictly-positive-real.  So it FAILS the bare (B-iii) positivity clause.  This
    is the DOCUMENTED over-sharpness of bare positivity: it selects zeta ALONE among
    Euler products; B-mult-twisted is the correct arithmetic-class primitive."""
    m = result["matrix"]["l_chi5"]
    assert m["weight_positivity"]["verdict"] == zoo.FAIL
    # zeta (trivial twist) still passes bare positivity: the two are genuinely different
    assert result["matrix"]["zeta"]["weight_positivity"]["verdict"] == zoo.PASS


def test_l_function_grh_conditional_labels(result):
    """W3c: L(chi) is a genuine L-function -- density/temperedness unconditional, but
    pure-pointness and defect-0 are GRH-CONDITIONAL, EXACTLY zeta's status."""
    m = result["matrix"]["l_chi5"]
    assert m["support_density"]["verdict"] == zoo.PASS
    assert m["temperedness"]["verdict"] == zoo.PASS
    assert m["atomic_spectrum"]["verdict"] == zoo.COND    # GRH, never unqualified PASS
    assert m["defect_bounded"]["verdict"] == zoo.COND     # k=0 <=> GRH


def test_dh_is_nonmultiplicative_sum_of_passing_Ls(result):
    """W3c -- THE POINT: DH = (1-ik)/2 L(chi) + (1+ik)/2 L(chi-bar) is the
    NON-MULTIPLICATIVE SUM of two objects that each PASS B-mult-twisted, yet DH
    itself STILL FAILS B-mult (composite atom b(6)!=0).  Multiplicativity is not
    preserved under linear combination -- exactly why it discriminates DH."""
    assert result["matrix"]["l_chi5"]["multiplicativity"]["verdict"] == zoo.PASS
    assert result["matrix"]["dh"]["multiplicativity"]["verdict"] == zoo.FAIL
    assert "COMPOSITE" in result["matrix"]["dh"]["multiplicativity"]["detail"]


def test_bmult_twisted_admits_arithmetic_class_not_zeta_alone(result):
    """W3c resolves the class-not-description objection: B-mult-twisted admits BOTH
    zeta and L(chi) (the arithmetic class) while excluding DH, generic FQ, lattice,
    random.  It is a genuine CLASS predicate, not a description of zeta alone."""
    vk = result["variant_kill"]
    assert vk["Bm"]["zeta"]["survives"]
    assert vk["Bm"]["l_chi5"]["survives"]
    for other in ("dh", "lattice", "ksly", "random"):
        assert vk["Bm"][other]["killed"], f"{other} must be killed by B-mult-twisted"


def test_broken_character_twist_forged_control_flips(result):
    """W3c forged negative control: corrupting a single character value (chi(2)=0.5,
    breaking |chi(2)|=1 and complete multiplicativity) makes the generation law fail
    -> the genuine L(chi) PASS flips to FAIL, proving the twisted clause is a real
    function of the character data, not a descriptor lookup."""
    fc = next(c for c in result["forged_controls"]
              if c["control"] == "broken_character_twist")
    assert fc["flipped"]
    assert fc["genuine"] == zoo.PASS and fc["forged_verdict"] == zoo.FAIL


def test_l_chi5_eval_rigorous_and_reconstructs_dh():
    """The certified L-driver: l_chi5_eval encloses L(s,chi) (cross-checked vs a
    high-precision reference), and the DH identity closes through the two L balls:
    (1-ik)/2 L(chi) + (1+ik)/2 L(chi-bar) == D(s)."""
    try:
        from telperion.arb_dh import l_chi5_eval, dh_eval, dh_kappa_interval, DH_AVAILABLE
    except Exception:
        pytest.skip("arb_dh unavailable")
    if not DH_AVAILABLE:
        pytest.skip("libflint acb_dirichlet_hurwitz unavailable")

    def mid(box):
        a, b, c, d = [float(x) for x in box]
        return complex((a + b) / 2, (c + d) / 2)

    lchi = mid(l_chi5_eval("4/5", "857/10", 160, conj=False))
    lbar = mid(l_chi5_eval("4/5", "857/10", 160, conj=True))
    klo, khi = dh_kappa_interval(160)
    k = float((klo + khi) / 2)
    dh_recon = (1 - 1j * k) / 2 * lchi + (1 + 1j * k) / 2 * lbar
    dh_direct = mid(dh_eval("4/5", "857/10", 160))
    assert abs(dh_recon - dh_direct) < 1e-10, (
        f"DH reconstruction from L balls off: {dh_recon} vs {dh_direct}")


def test_corrupted_certified_input_flips_verdict(result):
    """The load-bearing negative control: corrupting the DH off-line flag must flip
    the defect verdict, proving verdicts are a real function of the certified data."""
    fc = next(c for c in result["forged_controls"]
              if c["control"] == "corrupt_dh_offline_flag")
    assert fc["flipped"]
    assert fc["genuine"] == zoo.FAIL and fc["forged_verdict"] == zoo.PASS
