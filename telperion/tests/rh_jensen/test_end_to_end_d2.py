"""End-to-end test: d=2 Jensen hyperbolicity certificate (Task 6 MILESTONE).

conjecture1_proved = False. This test verifies the full pipeline:
  1. generate.py --degree 2 --n 0 runs without error and writes JensenHyperbolicity.lean.
  2. The written file contains no "sorry".
  3. The file contains the AXLE statement-match example (kernel-enforced type check).
  4. lake build (SoC-safe: cache-get then build) exits 0, confirming the Lean kernel
     accepts the theorem and the AXLE gate.

This is the FIRST kernel-verified J^{2,0} hyperbolicity certificate for the
Riemann zeta function. NOT a proof of RH.
"""
from __future__ import annotations

import pytest
pytest.importorskip("flint")

import shutil
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]  # .../telperion
LEAN_DIR = REPO_ROOT / "examples" / "jensen_hyperbolicity" / "lean"
LEAN_FILE = LEAN_DIR / "JensenHyperbolicity.lean"
GENERATE_SCRIPT = REPO_ROOT / "examples" / "jensen_hyperbolicity" / "generate.py"

PYTHON = sys.executable
LAKE = shutil.which("lake") or __import__("os").path.expanduser("~/.elan/bin/lake")


def test_generate_writes_lean_no_sorry() -> None:
    """generate.py --degree 2 --n 0 writes a .lean file that contains no sorry."""
    result = subprocess.run(
        [PYTHON, str(GENERATE_SCRIPT), "--degree", "2", "--n", "0", "--prec", "300"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, (
        f"generate.py exited {result.returncode}\n"
        f"stdout: {result.stdout}\n"
        f"stderr: {result.stderr}"
    )
    assert LEAN_FILE.exists(), f"JensenHyperbolicity.lean not written to {LEAN_FILE}"
    content = LEAN_FILE.read_text()
    assert "sorry" not in content, (
        "JensenHyperbolicity.lean contains 'sorry' -- emitter must produce a sorry-free cert."
    )


def test_generated_lean_contains_axle_gate() -> None:
    """The emitted file contains the AXLE statement-match example."""
    assert LEAN_FILE.exists(), f"JensenHyperbolicity.lean not found at {LEAN_FILE}"
    content = LEAN_FILE.read_text()
    # The AXLE gate is an `example` with the same box bounds as the theorem,
    # closed by `:= jensen_box_hyperbolic_deg2_0`.
    assert "AXLE statement-match gate" in content, (
        "AXLE gate comment not found in JensenHyperbolicity.lean"
    )
    assert "jensen_box_hyperbolic_deg2_0" in content.split("AXLE statement-match gate")[1], (
        "AXLE example proof `jensen_box_hyperbolic_deg2_0` not found after AXLE gate comment"
    )
    assert ".roots.card = 2" in content, (
        "Conclusion .roots.card = 2 not found in JensenHyperbolicity.lean"
    )


def test_generated_lean_contains_theorem() -> None:
    """The file declares the expected theorem name."""
    assert LEAN_FILE.exists(), f"JensenHyperbolicity.lean not found at {LEAN_FILE}"
    content = LEAN_FILE.read_text()
    assert "theorem jensen_box_hyperbolic_deg2_0" in content, (
        "theorem jensen_box_hyperbolic_deg2_0 not found in JensenHyperbolicity.lean"
    )


@pytest.mark.skipif(shutil.which("lake") is None, reason="lake not available")
def test_generated_lean_builds_green() -> None:
    """lake build succeeds (SoC-safe: cache-get then build).

    This test is the AXLE gate: the Lean kernel must accept both the theorem proof
    and the statement-match example. A type mismatch in the AXLE example would
    cause a build failure.
    """
    # SoC-safe: always pull cache before building to avoid triggering a
    # from-scratch Mathlib compile on the Mac (hundreds of Mathlib.* jobs = risk).
    cache_result = subprocess.run(
        [LAKE, "exe", "cache", "get"],
        cwd=str(LEAN_DIR),
        capture_output=True,
        text=True,
        timeout=120,
    )
    # cache get is best-effort; proceed even if it reports nothing new.
    _ = cache_result

    build_result = subprocess.run(
        [LAKE, "build"],
        cwd=str(LEAN_DIR),
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert build_result.returncode == 0, (
        f"lake build exited {build_result.returncode}\n"
        f"stdout: {build_result.stdout}\n"
        f"stderr: {build_result.stderr}"
    )
    # Confirm the axioms line appears (shows #print axioms ran).
    combined = build_result.stdout + build_result.stderr
    assert "jensen_box_hyperbolic_deg2_0" in combined, (
        "Expected theorem name not found in lake build output"
    )


def test_check_mode_passes() -> None:
    """generate.py --check returns 0 when the on-disk file matches a fresh render."""
    result = subprocess.run(
        [PYTHON, str(GENERATE_SCRIPT), "--degree", "2", "--n", "0", "--prec", "300", "--check"],
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, (
        f"generate.py --check failed (on-disk file does not match fresh render)\n"
        f"stdout: {result.stdout}\n"
        f"stderr: {result.stderr}"
    )
    assert "OK" in result.stdout, (
        f"Expected 'OK' in check output, got: {result.stdout}"
    )
