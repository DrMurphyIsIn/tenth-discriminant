"""pytest configuration for rh_jensen tests.

Provides a session-scoped autouse fixture that snapshots JensenHyperbolicity.lean
before any test runs and restores it unconditionally after the session ends.

This makes every test in this directory non-destructive: tests that regenerate
the file (e.g. --n 0 single-cert mode or --n-list subset mode) cannot leave
the working tree dirty after the suite finishes, regardless of pass/fail order.
"""
from __future__ import annotations

import pytest
from pathlib import Path

_LEAN_FILE = (
    Path(__file__).resolve().parents[2]
    / "examples"
    / "jensen_hyperbolicity"
    / "lean"
    / "JensenHyperbolicity.lean"
)


@pytest.fixture(scope="session", autouse=True)
def restore_jensen_lean_file():
    """Snapshot JensenHyperbolicity.lean before the session; restore it after.

    The teardown runs unconditionally (try/finally), so the committed canonical
    3-theorem grid (n=0,1,2) is always left in place after the suite, even when
    a test fails mid-run or is interrupted.
    """
    canonical: str | None = None
    if _LEAN_FILE.exists():
        canonical = _LEAN_FILE.read_text(encoding="utf-8")

    yield  # run the entire test session

    if canonical is not None:
        _LEAN_FILE.write_text(canonical, encoding="utf-8")
