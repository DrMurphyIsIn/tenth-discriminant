"""`heavy_build_targets`: the heavy judge on an island with no Arb4 ladder (HODGE-1, 2026-10-13).

A `judge_via = "heavy"` node may list the island modules missions-comparator-heavy.yml must build,
ONE AT A TIME and in order, before its challenge (the HODGE-1 certificates peak at 13.4 GB on the
16 GB runner). Without the field the workflow discovers the Arb4_h<H> ladder segments exactly as
before. Pins:
  (a) a heavy node with heavy_build_targets plans exactly those targets, in order, and the
      workflow's build step runs one `lake build` per target in that order, then the challenge;
  (b) the existing Arb4 ladder heavy node still discovers its segments as before;
  (c) the refusal gate still refuses a non-heavy node (exit 2), --build-plan included;
plus schema validation / round-trip of the field, and that no AxiomGuard* module pulls in a
HODGE-1 certificate module.
"""
import json
import os
import re
import shutil
import subprocess
from pathlib import Path

import pytest

yaml = pytest.importorskip("yaml")

from telperion.missions import judge
from telperion.missions.schema import SchemaError, load_node, save_node

T = Path(__file__).resolve().parents[1]           # telperion/
WF = T.parent / ".github" / "workflows" / judge.HEAVY_WORKFLOW
LADDER = "AND_ladder_h8000_kernel"
ORDINARY = "AND_theta_branch"
RVM = T / "examples" / "rvm_bridge" / "lean"
HODGE1_TARGETS = [l.strip() for l in (RVM / "hodge1_heavy_modules.txt").read_text().splitlines()
                  if l.strip()]


def _node_toml(**extra) -> str:
    lines = ['name = "HODGE1.window_5493"', 'title = "t"', 'kind = "milestone"',
             'status = "draft"', 'statement_module = "Statements.HODGE1_window_5493"']
    for k, v in extra.items():
        lines.append(f"{k} = {json.dumps(v)}")
    return "\n".join(lines) + "\n"


def _fake_root(tmp_path: Path, toml: str) -> Path:
    root = tmp_path / "telperion"
    (root / "missions" / "hodge" / "nodes").mkdir(parents=True)
    (root / "missions" / "hodge" / "nodes" / "HODGE1_window_5493.toml").write_text(toml)
    lean = root / "examples" / "rvm_bridge" / "lean"
    lean.mkdir(parents=True)
    (lean / "lakefile.toml").write_text('name = "x"\n')
    # A stray ladder segment: mode=targets must ignore it.
    (lean / "Arb4_h1000.lean").write_text("")
    return root


# (a) ---------------------------------------------------------------------------------------

def test_targets_plan_is_exactly_the_listed_modules_in_order(tmp_path):
    root = _fake_root(tmp_path, _node_toml(judge_via="heavy",
                                           heavy_build_targets=HODGE1_TARGETS))
    plan = judge.heavy_build_plan(root, "rvm_bridge", "HODGE1_window_5493")
    assert plan == {"mode": "targets", "targets": HODGE1_TARGETS, "segments": []}
    assert "Hodge1_Window5493" in plan["targets"]


def test_workflow_builds_targets_one_at_a_time_in_order_then_the_challenge(tmp_path):
    """Run the judge job's real build step with stub `lake` and `/usr/bin/time`: one
    `lake build <m>` per target, in the listed order, each under time -v, then the bridge."""
    if not shutil.which("bash"):
        pytest.skip("needs bash")
    steps = yaml.safe_load(WF.read_text())["jobs"]["judge-part"]["steps"]
    script = next(s for s in steps if s.get("name", "").startswith("Build the bridge module"))["run"]
    bindir = tmp_path / "bin"
    bindir.mkdir()
    log = tmp_path / "lake.log"
    (bindir / "lake").write_text(f'#!/usr/bin/env bash\necho "lake $*" >> "{log}"\n')
    (bindir / "faketime").write_text(
        '#!/usr/bin/env bash\n[ "$1" = -v ] && [ "$2" = -o ] || exit 97\nout="$3"; shift 3\n'
        f'echo "time $*" >> "{log}"\n'
        '"$@"; rc=$?\necho "	Maximum resident set size (kbytes): 4242" > "$out"\nexit $rc\n')
    for f in bindir.iterdir():
        f.chmod(0o755)
    assert script.count("/usr/bin/time -v -o") == 1
    script = script.replace("/usr/bin/time", str(bindir / "faketime"))
    rt = tmp_path / "rt"
    rt.mkdir()
    (rt / "nodes.tsv").write_text("HODGE1_window_5493\tc.json\tHodge1_Window5493\tthm\tbr\t"
                                  "lean-kernel-only\t\t\n")
    (rt / "heavy_targets.txt").write_text("\n".join(HODGE1_TARGETS) + "\n")
    bundle = tmp_path / "bundle"
    bundle.mkdir()
    island = tmp_path / "island"
    island.mkdir()
    env = dict(os.environ, PATH=f"{bindir}:{os.environ['PATH']}", RUNNER_TEMP=str(rt),
               BUNDLE=str(bundle))
    r = subprocess.run(["bash", "-c", script], cwd=island, env=env, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    calls = log.read_text().splitlines()
    expect = []
    for m in HODGE1_TARGETS:
        expect += [f"time lake build {m}", f"lake build {m}"]
    expect.append("lake build MissionChallenges.HODGE1_window_5493")
    assert calls == expect
    assert r.stdout.count("PEAK RSS ") == len(HODGE1_TARGETS)
    assert "PEAK RSS Hodge1_Window5493 4242 kB" in r.stdout


def test_heavy_seg_matrix_only_runs_in_segments_mode():
    jobs = yaml.safe_load(WF.read_text())["jobs"]
    assert jobs["heavy-seg"]["if"].replace(" ", "") == "${{needs.validate.outputs.mode=='segments'}}"
    jp = jobs["judge-part"]["if"]
    assert "!cancelled()" in jp and "needs.heavy-seg.result == 'success'" in jp
    assert "needs.validate.outputs.mode == 'targets' && needs.heavy-seg.result == 'skipped'" in jp
    dl = next(s for s in jobs["judge-part"]["steps"]
              if s.get("name", "").startswith("Collect the segment leaf builds"))
    assert "mode == 'segments'" in dl["if"]


def test_peak_rss_is_logged_around_heavy_builds_and_comparator():
    jobs = yaml.safe_load(WF.read_text())["jobs"]
    seg = next(s for s in jobs["heavy-seg"]["steps"] if "Edges_" in s.get("run", ""))["run"]
    assert '/usr/bin/time -v -o "$RUNNER_TEMP/time_$m.txt" lake build "+$m"' in seg
    assert "PEAK RSS $m" in seg
    cmp = next(s for s in jobs["judge-part"]["steps"]
               if s.get("name", "").startswith("Comparator on the heavy node"))["run"]
    assert '/usr/bin/time -v -o "$RUNNER_TEMP/time_comparator.txt" lake env comparator "$cfg"' in cmp
    assert cmp.count("PEAK RSS comparator:$slug") == 2   # on PASS and on FAIL


# (b) ---------------------------------------------------------------------------------------

def test_ladder_node_still_discovers_its_segments(capsys):
    assert judge.main(["--island", "zeta_reflection", "--heavy", "--only", LADDER,
                       "--build-plan"]) == 0
    plan = json.loads(capsys.readouterr().out)
    assert plan == {"mode": "segments", "targets": [], "segments": [h * 1000 for h in range(1, 9)]}


def test_segment_discovery_matches_the_old_shell_pipeline():
    lean = T / "examples" / "zeta_reflection" / "lean"
    old = sorted(int(m.group(1)) for p in lean.iterdir()
                 if (m := re.match(r"^Arb4_h([0-9]*)\.lean$", p.name)) and m.group(1))
    assert judge.ladder_segments(lean) == old and old


def test_no_ladder_and_no_targets_fails_loudly(tmp_path):
    root = _fake_root(tmp_path, _node_toml(judge_via="heavy"))
    (root / "examples" / "rvm_bridge" / "lean" / "Arb4_h1000.lean").unlink()
    with pytest.raises(judge.JudgeError, match="heavy_build_targets"):
        judge.heavy_build_plan(root, "rvm_bridge", "HODGE1_window_5493")


# (c) ---------------------------------------------------------------------------------------

def test_refusal_gate_still_refuses_a_non_heavy_node(capsys):
    for extra in ([], ["--build-plan"], ["--configs"]):
        assert judge.main(["--island", "zeta_reflection", "--heavy", "--only", ORDINARY,
                           *extra]) == 2
        assert "not 'heavy'" in capsys.readouterr().err


def test_build_plan_needs_heavy_and_one_node(capsys):
    assert judge.main(["--island", "zeta_reflection", "--only", ORDINARY, "--build-plan"]) == 2


# schema ------------------------------------------------------------------------------------

def test_schema_validates_and_round_trips_heavy_build_targets(tmp_path):
    p = tmp_path / "n.toml"
    p.write_text(_node_toml(judge_via="heavy", heavy_build_targets=HODGE1_TARGETS))
    n = load_node(p)
    assert n.heavy_build_targets == tuple(HODGE1_TARGETS) and n.extra is None
    save_node(n, p)
    assert load_node(p).heavy_build_targets == tuple(HODGE1_TARGETS)
    assert "heavy_build_targets" in p.read_text()


@pytest.mark.parametrize("bad", ["Hodge1_Window5493", ["+Hodge1_Cert45E"], ["a b"], [1],
                                 ["Hodge1_Par45", "Hodge1_Par45"], ["Hodge1:olean"]])
def test_schema_rejects_malformed_targets(tmp_path, bad):
    p = tmp_path / "n.toml"
    p.write_text(_node_toml(judge_via="heavy", heavy_build_targets=bad))
    with pytest.raises(SchemaError, match="heavy_build_targets"):
        load_node(p)


def test_schema_rejects_targets_without_judge_via_heavy(tmp_path):
    p = tmp_path / "n.toml"
    p.write_text(_node_toml(heavy_build_targets=["Hodge1_Window5493"]))
    with pytest.raises(SchemaError, match="judge_via"):
        load_node(p)


# AxiomGuard isolation ----------------------------------------------------------------------

def _imports(lean_dir: Path, mod: str):
    f = lean_dir / (mod.replace(".", "/") + ".lean")
    if not f.is_file():
        return []
    return re.findall(r"(?m)^import\s+([\w.]+)", f.read_text())


#: The only Hodge1 modules allowed in the AxiomGuard* closure: the light registry shape of the
#: one-prime identity (#717, imported by AxiomGuardRvMBridge for its guard anchor) and its light
#: imports. None of them touches a certificate.
LIGHT_HODGE1_IN_GUARD = {"Hodge1_RegOnePrime", "Hodge1_Reduction", "Hodge1_Strip"}


def test_no_axiomguard_module_pulls_in_hodge1():
    """The per-PR judge imports every AxiomGuard* lib into rvm_bridge challenges; a HODGE-1
    certificate in that closure would put 13.4 GB builds back on the per-PR path. Only the
    light modules in LIGHT_HODGE1_IN_GUARD may appear."""
    guards = judge.island_guard_modules(RVM)
    assert guards and not any("Hodge1" in g for g in guards)
    seen, todo = set(), list(guards)
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        todo += [i for i in _imports(RVM, m) if (RVM / (i.replace(".", "/") + ".lean")).is_file()]
    hodge1 = {m for m in seen if m.startswith("Hodge1")}
    assert hodge1 <= LIGHT_HODGE1_IN_GUARD, sorted(hodge1 - LIGHT_HODGE1_IN_GUARD)
    heavy = {l.strip() for l in (RVM / "hodge1_heavy_modules.txt").read_text().splitlines() if l.strip()}
    assert not ({m for m in heavy if "Cert" in m or "Ldl" in m or "Window" in m} & seen)
