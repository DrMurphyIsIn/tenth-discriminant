"""The core/bg boundary is the whole point of the split: the general engine
(``telperion.*``) must not depend on the Brualdi-Goldwasser research lab
(``telperion.bg.*``).  The trust-model claim — *a referee audits the small
engine, not the research accretion* — is only true if this holds, so it is
enforced here, statically (no core source imports bg) and dynamically
(``import telperion`` drags in zero bg modules).
"""
import ast
import os
import subprocess
import sys
from pathlib import Path

import pytest

SRC = Path(__file__).resolve().parents[1] / "src"
CORE_DIR = SRC / "telperion"
BG_DIR = CORE_DIR / "bg"


def _core_module_files():
    """Every .py directly under telperion/ (the engine) — NOT telperion/bg/."""
    for fn in sorted(os.listdir(CORE_DIR)):
        if fn.endswith(".py"):
            yield CORE_DIR / fn


def test_bg_package_exists():
    assert BG_DIR.is_dir(), "telperion/bg/ must exist"
    assert (BG_DIR / "__init__.py").is_file()


@pytest.mark.parametrize("path", list(_core_module_files()), ids=lambda p: p.name)
def test_core_module_does_not_import_bg(path):
    """Static guard: no engine module may import from telperion.bg, in any
    spelling (`from telperion.bg`, `import telperion.bg`, `from .bg`,
    `from ..bg`)."""
    tree = ast.parse(path.read_text(), filename=str(path))
    offenders = []
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            # relative `.bg` / `..bg`
            if node.level and (mod == "bg" or mod.startswith("bg.")):
                offenders.append(f"from {'.' * node.level}{mod} import ...")
            if mod == "telperion.bg" or mod.startswith("telperion.bg."):
                offenders.append(f"from {mod} import ...")
        elif isinstance(node, ast.Import):
            for a in node.names:
                if a.name == "telperion.bg" or a.name.startswith("telperion.bg."):
                    offenders.append(f"import {a.name}")
    assert not offenders, f"{path.name} imports the bg research lab: {offenders}"


def test_importing_core_loads_no_bg_modules():
    """Dynamic guard: a fresh `import telperion` must not transitively import
    any telperion.bg submodule."""
    code = (
        "import sys; "
        "import telperion; "
        "bg=[m for m in sys.modules if m.startswith('telperion.bg')]; "
        "print(','.join(bg))"
    )
    env = dict(os.environ, PYTHONPATH=str(SRC))
    out = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, env=env
    )
    assert out.returncode == 0, out.stderr
    leaked = out.stdout.strip()
    assert leaked == "", f"`import telperion` leaked bg modules: {leaked}"


def test_bg_namespace_is_a_superset():
    """telperion.bg re-exports the engine, so it is a strict superset — this is
    what lets consumers import everything from one namespace."""
    sys.path.insert(0, str(SRC))
    import telperion
    import telperion.bg as bg

    missing = [s for s in ("certify", "emit", "InequalityFamily", "freeze")
               if not hasattr(bg, s)]
    assert not missing, f"telperion.bg missing engine symbols: {missing}"
    # and it carries bg-only symbols
    assert hasattr(bg, "bg_phi11"), "telperion.bg missing its own symbols"
    assert not hasattr(telperion, "bg_phi11"), "bg symbol leaked into core"
