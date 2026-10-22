"""The li-positivity CI guard floor must equal the guard file's anchor count.

The `li-positivity-compiles` job in .github/workflows/telperion-lean-e2e.yml fails when
AxiomGuardLiPositivity.lean prints fewer than N axiom lines. N was 146 while the file grew to
264 anchors, so the guard could silently lose 118 of them (45%) and stay green. This pins N to
the file: adding anchors without raising the floor, or lowering the floor, fails here.
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github" / "workflows" / "telperion-lean-e2e.yml"
GUARD = ROOT / "telperion" / "examples" / "li_positivity" / "lean" / "AxiomGuardLiPositivity.lean"


def _anchor_count() -> int:
    return sum(1 for line in GUARD.read_text(encoding="utf-8").splitlines()
               if line.startswith("#print axioms"))


def _floor() -> int:
    text = WORKFLOW.read_text(encoding="utf-8")
    start = text.index("  li-positivity-compiles:")
    step = text.index("lake env lean AxiomGuardLiPositivity.lean", start)
    m = re.search(r'if \[ "\$n" -lt "(\d+)" \]', text[step:step + 2000])
    assert m, "could not find the guard floor in the li-positivity-compiles job"
    return int(m.group(1))


def test_floor_equals_the_guard_files_anchor_count():
    assert _anchor_count() > 0
    assert _floor() == _anchor_count(), (
        f"li-positivity guard floor is {_floor()} but AxiomGuardLiPositivity.lean has "
        f"{_anchor_count()} `#print axioms` anchors; set the floor in telperion-lean-e2e.yml to match")
