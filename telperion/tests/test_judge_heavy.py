"""judge_via = "heavy": excluded from the per-PR bundle BY RULE, judged by the heavy workflow.

Pins the five guarantees agreed with the CI-governance owner (2026-09-26):
  1. the committed bundle omits heavy nodes and `--check` passes in that state (so nobody
     "fixes" a future mismatch by re-adding one);
  2. the heavy path REFUSES a node that is not judge_via = "heavy";
  3. heavy nodes are rendered Lean-kernel-only (heavy_certificates also set);
  4. a heavy bundle is never checked or written over the committed one;
  5. provenance-report shows a heavy node as judged elsewhere, not as an oversight.
"""
import json
from pathlib import Path

import pytest

pytest.importorskip("yaml")

from telperion.missions import judge
from telperion.missions.schema import SchemaError, _judge_via

T = Path(__file__).resolve().parents[1]           # telperion/
HEAVY = "AND_ladder_h8000_kernel"
ORDINARY = "AND_theta_branch"
BUNDLE = T / "missions" / "judge" / "zeta_reflection"


def test_committed_bundle_excludes_heavy_and_checks_clean():
    assert not (BUNDLE / "MissionChallenges" / f"{HEAVY}.lean").exists()
    assert not (BUNDLE / f"{HEAVY}.comparator.json").exists()
    assert HEAVY not in (BUNDLE / "MissionChallenges.lean").read_text()
    man = json.loads((BUNDLE / "MANIFEST.json").read_text())
    assert HEAVY not in {n["slug"] for n in man["nodes"]}
    assert {"node": f"anduril/{HEAVY}", "judge_via": "heavy",
            "workflow": judge.HEAVY_WORKFLOW} in man["judged_elsewhere"]
    b = judge.build_bundle(T, "zeta_reflection")
    assert f"anduril/{HEAVY}" in b.excluded
    assert judge.check_bundle(b, BUNDLE) == []


def test_heavy_path_refuses_ordinary_node():
    with pytest.raises(judge.JudgeError, match="not 'heavy'"):
        judge.build_bundle(T, "zeta_reflection", heavy=True, only=[ORDINARY])


def test_heavy_path_needs_named_nodes():
    with pytest.raises(judge.JudgeError, match="--only"):
        judge.build_bundle(T, "zeta_reflection", heavy=True)


def test_heavy_render_is_lean_kernel_only_and_compositional_for_h8000():
    """h8000 carries a [compose] table (2026-09-27), so the heavy render is its PARTS -- one per
    segment plus the implication -- never the one-closure capstone challenge."""
    b = judge.build_bundle(T, "zeta_reflection", heavy=True, only=[HEAVY])
    slugs = [c.slug for c in b.challenges]
    assert HEAVY not in slugs
    assert slugs == [f"{HEAVY}__seg_h{h}000" for h in range(1, 9)] + [f"{HEAVY}__compose"]
    assert all(c.nanoda is False for c in b.challenges)
    assert b.excluded == ()


def test_heavy_bundle_is_never_checked_or_written_in_place(capsys):
    assert judge.main(["--island", "zeta_reflection", "--heavy", "--only", HEAVY, "--check"]) == 2
    assert judge.main(["--island", "zeta_reflection", "--heavy", "--only", HEAVY]) == 2


def test_heavy_bundle_require_path_resolves_from_any_out(tmp_path):
    out = tmp_path / "somewhere" / "deep"
    assert judge.main(["--island", "zeta_reflection", "--heavy", "--only", HEAVY,
                       "--out", str(out)]) == 0
    line = next(l for l in (out / "lakefile.toml").read_text().splitlines() if l.startswith("path = "))
    rel = line.split('"')[1]
    assert (out / rel / "lakefile.toml").is_file()


def test_judge_via_value_is_validated():
    assert _judge_via("heavy") == "heavy" and _judge_via("") == ""
    with pytest.raises(SchemaError):
        _judge_via("sometimes")


def test_provenance_report_names_the_heavy_workflow():
    """Unrecorded: the node is shown as judged elsewhere, not as an oversight.  Recorded (the
    live state since run 36306561345): covered, and flagged COMPOSITIONAL, never as a plain pass."""
    import dataclasses
    from telperion.missions.provenance import render_provenance_report
    from telperion.missions.registry import load_campaign
    camp = load_campaign(T / "missions" / "anduril")
    text = render_provenance_report(camp)
    assert "COMPOSITIONAL: the capstone's own proof was not replayed" in text
    camp.nodes[HEAVY] = dataclasses.replace(camp.nodes[HEAVY], comparator=None)
    text = render_provenance_report(camp)
    i = text.index(HEAVY)
    assert "judge_via = heavy" in text[i:i + 400] and judge.HEAVY_WORKFLOW in text[i:i + 400]
    assert "no heavy-judge run recorded yet" in text[i:i + 400]


def test_heavy_workflow_constant_names_an_existing_workflow():
    """provenance-report points readers at judge.HEAVY_WORKFLOW; a rename must not leave it stale."""
    wf = Path(__file__).resolve().parents[2] / ".github" / "workflows" / judge.HEAVY_WORKFLOW
    assert wf.is_file(), f"judge.HEAVY_WORKFLOW = {judge.HEAVY_WORKFLOW!r} names no workflow file"
