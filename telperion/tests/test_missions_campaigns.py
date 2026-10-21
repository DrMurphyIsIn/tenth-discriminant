"""The real campaigns' invariants run in CI: a hand-edited status cannot pass.

The design's central promise is that the registry never claims more than CI
can re-check (spec section 7). The fixture-only tests cover the machinery;
these cover the DATA.

Campaigns are DISCOVERED (every missions/*/mission.toml), not enumerated:
the bg/rh-only hardcoding let ANDURIL + MIRRORMERE land 23 unpinned
statement headers with pytest green (caught 2026-09-14, fixed alongside
this parametrization).
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
from telperion.missions.verify import verify_campaign  # noqa: E402

MISSIONS = Path(__file__).resolve().parents[1] / "missions"
CAMPAIGNS = sorted(p.parent.name for p in MISSIONS.glob("*/mission.toml"))


def test_campaigns_are_discovered():
    # The discovery glob must see the founding campaigns; an empty or
    # mis-rooted glob would turn the parametrized test into a silent no-op.
    assert {"bg", "rh"} <= set(CAMPAIGNS), CAMPAIGNS


@pytest.mark.parametrize("campaign", CAMPAIGNS)
def test_campaign_invariants_hold(campaign):
    report = verify_campaign(MISSIONS / campaign)
    assert report.ok, f"errors={report.errors} warnings={report.warnings}"
