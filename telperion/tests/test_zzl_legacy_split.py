"""The zzl_aux / zzl_legacy_boxes split (campaign.py): RHInBox_* boxes that no
non-box module imports go to the legacy package; consumed boxes stay in zzl_aux.
Pure-function test against a synthetic monolith on disk (no lake, no network)."""
from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest

_CAMPAIGN = Path(__file__).resolve().parents[1] / "examples" / "zeta_zero_localization" / "campaign.py"


@pytest.fixture(scope="module")
def campaign():
    spec = importlib.util.spec_from_file_location("zzl_campaign", _CAMPAIGN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _monolith(tmp_path: Path, libs: list[str], sources: dict[str, str]) -> Path:
    lean_dir = tmp_path / "lean"
    lean_dir.mkdir()
    (lean_dir / "lakefile.toml").write_text(
        'name = "mono"\n' + "".join(f'[[lean_lib]]\nname = "{n}"\n' for n in libs))
    for name, body in sources.items():
        (lean_dir / f"{name}.lean").write_text(body)
    return lean_dir


def test_split_keeps_consumed_boxes_and_moves_the_rest(campaign, tmp_path):
    libs = ["AllZeros_h100", "BraggDefect", "RHInBox_a", "RHInBox_b", "RHInBox_c",
            "RHInBoxT_band", "AllZeros_h1000", "AxiomGuardRHInBox"]
    lean_dir = _monolith(tmp_path, libs, {
        "AllZeros_h100": "import Mathlib\nimport RHInBox_a\n",
        "BraggDefect": "import Mathlib\n",
        "RHInBox_a": "import Mathlib\nimport RHInBox_b\n",   # transitive: b is consumed via a
        "RHInBox_b": "import Mathlib\n",
        "RHInBox_c": "import Mathlib\n",                    # nothing imports c -> legacy
    })
    aux = campaign.aux_modules(lean_dir)
    legacy = campaign.legacy_box_modules(lean_dir)
    assert aux == ["AllZeros_h100", "BraggDefect", "RHInBox_a", "RHInBox_b"]
    assert legacy == ["RHInBox_c"]
    # bands / chain capstones / the monolith-wide guard are in neither package
    for n in ("RHInBoxT_band", "AllZeros_h1000", "AxiomGuardRHInBox"):
        assert n not in aux and n not in legacy


def test_legacy_lakefile_is_a_named_package_with_its_targets(campaign):
    text = campaign.emit_aux_lakefile(["RHInBox_c", "RHInBox_d"], pkg_name=campaign.LEGACY_PKG)
    assert text.startswith('name = "zzl_legacy_boxes"\n')
    assert 'defaultTargets = ["RHInBox_c", "RHInBox_d"]' in text
    assert text.count("[[lean_lib]]") == 2
    assert 'name = "zzl_core"' in text  # same requires as zzl_aux


def test_aux_lakefile_default_name_unchanged(campaign):
    assert campaign.emit_aux_lakefile(["BraggDefect"]).startswith('name = "zzl_aux"\n')
