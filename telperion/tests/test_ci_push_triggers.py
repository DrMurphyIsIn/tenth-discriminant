"""Push triggers: restricted to main, and required unless a workflow is explicitly exempted.

A push to a pull-request branch already runs the workflow through the pull_request event;
running it a second time on the push event doubled the per-push runner load on an account
with a 20-job concurrency ceiling (2026-09-24). Required checks come from the pull_request run.

Post-merge verification of main needs a push trigger (2026-09-25). telperion-zeta-reflection had
none, so main was re-verified only by its weekly cron, and that cron never fired: GitHub dropped the
2026-09-23 slot. A cron can silently not run at all, which is worse than failing because it leaves
no red mark. So every workflow must have `push: branches: [main]` unless it is listed in
NO_PUSH_ALLOWED with the reason. That way a trigger cannot quietly disappear.
"""
from pathlib import Path

import pytest

yaml = pytest.importorskip("yaml")

_WF = Path(__file__).resolve().parents[2] / ".github" / "workflows"

#: Workflows allowed to have no push trigger, with the reason. Keep this list short and justified.
NO_PUSH_ALLOWED = {
    "missions-comparator-heavy.yml": (
        "Dispatch-only by design (2026-09-26): it judges one named judge_via = \"heavy\" node at a "
        "time, building the whole ladder across a matrix and, for a compositional node, running one "
        "Comparator job per part (~11 runner-hours in all). Per-merge runs would "
        "starve the 20-job ceiling. The per-PR missions-comparator covers every other node; "
        "provenance-report shows heavy nodes as judged here, with or without a recorded run."
    ),
    "telperion-legacy-boxes.yml": (
        "669 legacy box certificates at ~5.3 core-hours; nothing imports them. Cron + dispatch "
        "only, by cost decision (governance 2026-09-25). Mitigation: the weekly scheduled run "
        "and the ci-schedule-health watch (PR #640), which flags a schedule-only workflow that is "
        "red or has never fired."
    ),
}


def _on(wf):
    d = yaml.safe_load((_WF / wf).read_text())
    return d.get("on", d.get(True))


@pytest.mark.parametrize("wf", sorted(p.name for p in _WF.glob("*.yml")))
def test_push_trigger_is_main_only(wf):
    on = _on(wf)
    if not isinstance(on, dict) or "push" not in on:
        pytest.skip("no push trigger (presence is checked by test_push_trigger_present)")
    push = on["push"] or {}
    assert push.get("branches") == ["main"], f"{wf}: push trigger must be restricted to main"


@pytest.mark.parametrize("wf", sorted(p.name for p in _WF.glob("*.yml")))
def test_push_trigger_present(wf):
    on = _on(wf)
    has_push = isinstance(on, dict) and "push" in on
    if wf in NO_PUSH_ALLOWED:
        assert not has_push, f"{wf}: listed in NO_PUSH_ALLOWED but now has a push trigger; drop the exemption"
        return
    assert has_push, (f"{wf}: no push trigger on main, so main is never re-verified after a merge "
                      "(a cron is not enough: it can silently not fire). Add `push: branches: [main]` "
                      "(with a paths filter if the workflow is costly) or justify it in NO_PUSH_ALLOWED.")


def test_exemptions_exist():
    names = {p.name for p in _WF.glob("*.yml")}
    stale = sorted(set(NO_PUSH_ALLOWED) - names)
    assert not stale, f"NO_PUSH_ALLOWED lists workflows that no longer exist: {stale}"


import re as _re

_ZR = "telperion-zeta-reflection.yml"


def _glob_to_re(g):
    """GitHub path-filter glob -> regex: `**` crosses '/', `*` does not."""
    out, i = "", 0
    while i < len(g):
        if g.startswith("**", i):
            out += ".*"; i += 2
        elif g[i] == "*":
            out += "[^/]*"; i += 1
        else:
            out += _re.escape(g[i]); i += 1
    return _re.compile("^" + out + "$")


def _relevant():
    """The job-level RELEVANT regex (declared three times; all copies must agree)."""
    text = (_WF / _ZR).read_text()
    found = set(_re.findall(r"RELEVANT: '([^']+)'", text))
    assert len(found) == 1, f"{_ZR}: RELEVANT regex copies disagree: {len(found)} variants"
    return found.pop()


def _named_modules(rel):
    m = _re.search(r"zeta_zero_localization/lean/\((.*)\)\\\.lean\$", rel)
    assert m, "could not find the named-module group in RELEVANT"
    return m.group(1).split("|")


def _samples(rel):
    """Concrete paths the RELEVANT regex admits, one per alternative, plus every named module."""
    z = "telperion/examples/zeta_zero_localization/lean/"
    out = ["telperion/examples/zeta_reflection/lean/Some.lean",
           "telperion/examples/zeta_reflection/README.md",
           ".github/workflows/telperion-zeta-reflection.yml",
           "telperion/examples/zero_free_bridge/lean/Some.lean",
           "telperion/examples/zeta_zero_localization/lean/zzl_core/Some.lean"]
    for name in _named_modules(rel):
        if "[" in name:  # the RHInBoxT_* box-file family: instantiate one member
            out.append(z + "RHInBoxT_1d4000000_3999999d4000000_12d5_13d5.lean")
        else:
            out.append(z + name + ".lean")
    return out


def test_zeta_reflection_push_covers_relevant():
    """Every path the job treats as relevant must trigger the push run (no silent coverage gap)."""
    rel = _relevant()
    globs = [_glob_to_re(g) for g in _on(_ZR)["push"]["paths"]]
    for path in _samples(rel):
        assert _re.match(rel, path), f"sample {path} should match RELEVANT (test bug)"
        assert any(g.match(path) for g in globs), f"{path} is RELEVANT but no push path covers it"


def test_zeta_reflection_push_not_broader_than_relevant():
    """No push path may fire on files the job itself declares irrelevant (e.g. bulk AllZeros_h* bands)."""
    rel = _relevant()
    z = "telperion/examples/zeta_zero_localization/lean/"
    # AllZeros_h5000 WAS an irrelevant sample until the h8000 implication (#645) made the eight
    # ladder heights relevant; the bulk bands (h280000) and the rest stay irrelevant.
    irrelevant = [z + "AllZeros_h280000.lean", z + "AllZeros_h9000.lean", z + "AllZeros_h50000.lean",
                  z + "SomethingElse.lean", "telperion/examples/rvm_bridge/lean/X.lean"]
    globs = [_glob_to_re(g) for g in _on(_ZR)["push"]["paths"]]
    for path in irrelevant:
        assert not _re.match(rel, path), f"sample {path} should NOT match RELEVANT (test bug)"
        assert not any(g.match(path) for g in globs), f"push paths fire on irrelevant {path}"
    # and every push glob, instantiated, lands inside RELEVANT
    for g in _on(_ZR)["push"]["paths"]:
        inst = g.replace("**", "x/y.lean").replace("*", "12d5_13d5")
        assert _re.match(rel, inst), f"push path {g} admits {inst}, which RELEVANT rejects"


def test_zeta_reflection_covers_the_ladder_heights_the_implication_imports():
    """The compositional judge ties each AllZeros_h<H>.BandHyp by export hash, and the h8000
    implication imports AllZeros_h1000..h8000: an edit to any of them must re-run the ladder job
    (which compiles and island-checks the implication), both as RELEVANT and as a push path."""
    rel = _relevant()
    globs = [_glob_to_re(g) for g in _on(_ZR)["push"]["paths"]]
    z = "telperion/examples/zeta_zero_localization/lean/"
    for h in range(1, 9):
        path = f"{z}AllZeros_h{h}000.lean"
        assert _re.match(rel, path), f"{path} is imported by the h8000 implication but not RELEVANT"
        assert any(g.match(path) for g in globs), f"{path} has no push path"
    imports = _re.findall(r"(?m)^import\s+(AllZeros_h\d+)\s*$", (Path(__file__).resolve().parents[1]
        / "examples" / "zeta_reflection" / "lean" / "Arb4_Compose_h8000.lean").read_text())
    for m in imports:
        assert _re.match(rel, f"{z}{m}.lean"), f"implication import {m} is not RELEVANT"
