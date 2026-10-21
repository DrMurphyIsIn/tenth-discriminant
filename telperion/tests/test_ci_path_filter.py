"""The job-level path filter of .github/workflows/telperion-lean-e2e.yml.

Every island job must be gated on the `changes` job, fail OPEN (run everything when the
filter job did not succeed), run on workflow_dispatch and on the weekly schedule, and name
in its guard every island directory its own steps mention.  The filter list must contain
every island any job mentions.  A job whose guard is missing an island would silently stop
verifying that island; a filter missing an island would never run its job.
"""
import re
from pathlib import Path

import pytest

yaml = pytest.importorskip("yaml")

_WF = Path(__file__).resolve().parents[2] / ".github" / "workflows" / "telperion-lean-e2e.yml"
_ISLAND = re.compile(r"(?<![A-Za-z0-9_/])(?:telperion/)?examples/([A-Za-z0-9_]+)")


def _load():
    return yaml.safe_load(_WF.read_text())


def _islands_in(job: dict) -> set:
    return set(_ISLAND.findall(yaml.safe_dump(job)))


def test_changes_job_exists_and_is_first():
    d = _load()
    assert list(d["jobs"])[0] == "changes"
    step = [s for s in d["jobs"]["changes"]["steps"] if s.get("id") == "f"][0]
    assert step["uses"].startswith("dorny/paths-filter@")


def test_workflow_has_no_workflow_level_path_filter():
    d = _load()
    on = d.get("on", d.get(True))
    assert "paths" not in (on["push"] or {})
    assert on["pull_request"] is None or "paths" not in on["pull_request"]
    assert "schedule" in on and "workflow_dispatch" in on


#: Matrix jobs must NOT be path-guarded: a matrix job skipped by `if:` reports a single
#: unexpanded check, so its expanded required contexts never appear and the PR cannot merge.
UNGUARDED = {"mission-statements-compile"}


def test_matrix_jobs_are_not_guarded():
    d = _load()
    for jid, job in d["jobs"].items():
        if "strategy" in job and "matrix" in (job.get("strategy") or {}):
            assert jid in UNGUARDED and "if" not in job and job.get("needs") != "changes", jid


def test_every_island_job_is_guarded_fail_open():
    d = _load()
    for jid, job in d["jobs"].items():
        if jid == "changes" or jid in UNGUARDED:
            continue
        assert job.get("needs") == "changes", jid
        cond = job.get("if", "")
        assert cond.startswith("always() && (needs.changes.result != 'success'"), jid
        assert "github.event_name == 'workflow_dispatch'" in cond, jid
        assert "github.event_name == 'schedule'" in cond, jid
        assert "needs.changes.outputs.shared == 'true'" in cond, jid


def test_every_job_guard_names_every_island_its_steps_mention():
    d = _load()
    for jid, job in d["jobs"].items():
        if jid == "changes" or jid in UNGUARDED:
            continue
        for island in _islands_in({"steps": job["steps"]}):
            assert f"needs.changes.outputs.{island} == 'true'" in job["if"], (jid, island)


def test_filter_list_and_outputs_cover_every_island():
    d = _load()
    step = [s for s in d["jobs"]["changes"]["steps"] if s.get("id") == "f"][0]
    filters = yaml.safe_load(step["with"]["filters"])
    outputs = d["jobs"]["changes"]["outputs"]
    mentioned = set()
    for jid, job in d["jobs"].items():
        if jid != "changes":
            mentioned |= _islands_in({"steps": job["steps"]})
    assert mentioned <= set(filters), mentioned - set(filters)
    assert mentioned <= set(outputs), mentioned - set(outputs)
    for island in mentioned:
        assert filters[island] == [f"telperion/examples/{island}/**"], island
    assert ".github/workflows/telperion-lean-e2e.yml" in filters["shared"]
    assert filters["src"] == ["telperion/src/**"]
    assert filters["missions"] == ["telperion/missions/**"]


def test_jobs_that_run_python_depend_on_src_and_registry_readers_on_missions():
    d = _load()
    for jid, job in d["jobs"].items():
        if jid == "changes" or jid in UNGUARDED:
            continue
        body = yaml.safe_dump(job["steps"])
        cond = job["if"]
        if re.search(r"PYTHONPATH=src|generate\.py|python -m|telperion/src", body):
            assert "needs.changes.outputs.src == 'true'" in cond, jid
        if re.search(r"telperion/missions|missions/|mission ", body):
            assert "needs.changes.outputs.missions == 'true'" in cond, jid


def test_no_job_references_an_island_outside_the_filter():
    """A path outside telperion/examples would not be filtered; every island job must live there."""
    d = _load()
    for jid, job in d["jobs"].items():
        if jid in ("changes", "mission-statements-compile"):
            continue
        assert _islands_in({"steps": job["steps"]}), f"{jid} mentions no island directory"
