"""Kernel-COMPILE gate for UNIMODAL_PRELUDE (opt-in; runs where Mathlib is built).

The text lint in ``tests/test_bg_emitters.py`` only greps the prelude for
``sorry``/``axiom`` tokens -- which a proof that ERRORS-INTO-sorry silently
passes (the class of bug that shipped a broken ``unimodal_peak``).  This test
closes that gap: it feeds the prelude to the Lean kernel and asserts it compiles
to ZERO errors with clean axioms.

It reuses the repo's prebuilt Mathlib at ``examples/g1_floors/lean/.lake``.
Where that build is absent (e.g. a fresh worktree that has never run
``lake exe cache get``) the test SKIPS -- it is a CI/main gate, not a per-clone
requirement.
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[1]
_LEAN_PROJECT = _REPO / "examples" / "g1_floors" / "lean"

sys.path.insert(0, str(_REPO / "src"))
sys.path.insert(0, str(Path(__file__).resolve().parent))  # for the shared lean_env guard

from telperion import UNIMODAL_PRELUDE  # noqa: E402
from lean_env import lean_env_ready  # noqa: E402

_CLEAN_AXIOMS = "[propext, Classical.choice, Quot.sound]"


@pytest.mark.skipif(
    not lean_env_ready(_LEAN_PROJECT),
    reason="a prebuilt examples/g1_floors/lean Mathlib env is required "
    "(CI/main gate; skips -- never rebuilds -- in a fresh worktree)",
)
def test_unimodal_prelude_kernel_compiles():
    """The prelude must compile to zero errors with clean axioms -- catches a
    proof that errors into `sorryAx` (which the text lint would pass)."""
    src = (
        "import Mathlib\n\n"
        + UNIMODAL_PRELUDE
        + "\n#print axioms Telperion.unimodal_peak\n"
        + "#print axioms Telperion.climb_descend_of_ratio\n"
    )

    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", delete=False, encoding="utf-8"
    ) as fh:
        fh.write(src)
        lean_path = Path(fh.name)

    try:
        proc = subprocess.run(
            ["lake", "env", "lean", str(lean_path)],
            cwd=str(_LEAN_PROJECT),
            capture_output=True,
            text=True,
            timeout=600,
        )
    finally:
        lean_path.unlink(missing_ok=True)

    out = proc.stdout + proc.stderr
    assert proc.returncode == 0, (
        f"lean kernel-check failed (returncode {proc.returncode}):\n{out}"
    )
    # A proof that errored into sorry would surface `sorryAx` in the axioms.
    assert "sorryAx" not in out, f"prelude depends on sorryAx:\n{out}"
    # Both exported lemmas must report exactly the clean axiom set.
    for thm in ("Telperion.unimodal_peak", "Telperion.climb_descend_of_ratio"):
        assert f"'{thm}' depends on axioms: {_CLEAN_AXIOMS}" in out, (
            f"{thm} missing clean-axioms line:\n{out}"
        )
