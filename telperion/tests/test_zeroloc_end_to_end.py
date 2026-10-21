"""End-to-end test: first kernel-verified on-line nontrivial-zero count for zeta.

Tests that sign_change_count >= 5 on [10, 35] at half-integer sample spacing,
matching the 5 known nontrivial Riemann zeta zeros in that interval:
  t ~ 14.1347, 21.0220, 25.0109, 30.4249, 32.9351.

The enclosure hypotheses (enclose_lambda -> sign-definite real box) are
Arb-certified NON-KERNEL inputs; the sign-change counting and zero-existence
argument are kernel-clean.  conjecture1_proved = False.
"""
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

import os  # noqa: E402
import shutil  # noqa: E402

import pytest  # noqa: E402

import telperion.arb_enclosure as _ae  # noqa: E402
from telperion.arb_enclosure import enclose_lambda  # noqa: E402
from telperion.emit_xi_line_zeros import sign_change_count  # noqa: E402

# Optional-dependency guards: python-flint (Arb enclosures) and lake/Lean are not
# installed in the lightweight `unit` CI environment; these tests SKIP there rather
# than erroring, and run wherever the tools are present.
requires_flint = pytest.mark.skipif(
    not _ae._FLINT_AVAILABLE, reason="requires python-flint (Arb enclosures)"
)
_LAKE_PATH = os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ.get("PATH", "")
requires_lake = pytest.mark.skipif(
    shutil.which("lake", path=_LAKE_PATH) is None, reason="requires lake/Lean toolchain"
)


@requires_flint
def test_sign_changes_match_known_zero_count_10_to_35():
    # First nontrivial zeros (imag parts): 14.1347, 21.0220, 25.0109, 30.4249, 32.9351.
    # Sample densely on [10,35]; sign-change count must be >= 5 (the 5 known zeros in range).
    ts = [F(i, 2) for i in range(20, 71)]  # t = 10.0, 10.5, ..., 35.0
    samples = []
    for t in ts:
        (lo_re, hi_re), _ = enclose_lambda(F(1, 2), t, prec_bits=300)
        samples.append((t, (lo_re, hi_re)))
    assert sign_change_count(samples) >= 5


@requires_lake
def test_box_arg_principle_lambda_builds():
    """Task 5 (Stage 2C): the box argument principle for Lambda builds sorry-free.

    Composes three kernel-verified atoms at box B = [2/5, 3/5] x [10, 35] with the
    boundary split (H1) and the winding value (H4) as hypotheses.  Kernel-clean;
    conjecture1_proved = False.
    """
    import os
    import subprocess

    env = {**os.environ, "PATH": os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]}
    d = str(Path(__file__).resolve().parents[1] / "examples" / "zeta_zero_localization" / "lean")
    subprocess.run(["lake", "exe", "cache", "get"], cwd=d, env=env, check=True)
    r = subprocess.run(
        ["lake", "build", "BoxArgPrinciple"], cwd=d, env=env, capture_output=True, text=True
    )
    assert r.returncode == 0, r.stderr


@requires_lake
def test_zeta_blaschke_split_box_builds():
    """Task 7 (Stage 2B): the local Blaschke split of zeta'/zeta over the box is kernel-derived.

    `BlaschkeBox.zeta_blaschke_split_box` derives, on U = ball(cB, 13) containing the box
    B = [2/5, 3/5] x [10, 35], the split
      logDeriv zeta z = (sum_rho (divisor rho)/(z - rho)) + E z   (off the zeros)
    with E := logDeriv g HOLOMORPHIC on B, discharging Task 5's H2 (E-holomorphy) in kernel.
    `BoxArgPrincipleZeta.box_arg_principle_zeta` then instantiates the capstone with the derived
    split + error holomorphy (H1 derived from the split + boundary non-vanishing; H2 kernel).
    Both build sorry-free with clean axioms {propext, Classical.choice, Quot.sound}.
    conjecture1_proved = False.
    """
    import os
    import subprocess

    env = {**os.environ, "PATH": os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]}
    d = str(Path(__file__).resolve().parents[1] / "examples" / "zeta_zero_localization" / "lean")
    subprocess.run(["lake", "exe", "cache", "get"], cwd=d, env=env, check=True)
    r = subprocess.run(
        ["lake", "build", "BlaschkeBox", "BoxArgPrincipleZeta"],
        cwd=d,
        env=env,
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, r.stderr

    # Axiom hygiene: both key theorems depend only on the standard axioms (no sorryAx).
    axcheck = (
        "import BlaschkeBox\n"
        "import BoxArgPrincipleZeta\n"
        "#print axioms BlaschkeBox.zeta_blaschke_split_box\n"
        "#print axioms BoxArgPrincipleZeta.box_arg_principle_zeta\n"
        "#print axioms BoxArgPrincipleZeta.box_arg_principle_zeta'\n"
    )
    axfile = Path(d) / "AxCheckZetaSplit.lean"
    try:
        axfile.write_text(axcheck)
        ra = subprocess.run(
            ["lake", "env", "lean", str(axfile)], cwd=d, env=env, capture_output=True, text=True
        )
        assert ra.returncode == 0, ra.stderr
        assert "sorryAx" not in ra.stdout, ra.stdout
        assert "propext" in ra.stdout, ra.stdout
    finally:
        axfile.unlink(missing_ok=True)
