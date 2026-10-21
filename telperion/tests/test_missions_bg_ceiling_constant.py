"""The ceiling statement's rational bound must BE dns_phi11(4,5) — constant fidelity.

The BG_r2_multihub_ceiling statement hard-codes the DN-family peak as an exact
rational literal; this pins it to the generating Python (a drifted constant
would silently weaken or falsify the formal claim)."""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

def test_ceiling_literal_equals_dns_peak():
    from telperion.bg.double_near_star import dns_phi11
    stmt = (Path(__file__).resolve().parents[1] / "missions" / "bg" / "lean"
            / "Statements" / "BG_r2_multihub_ceiling.lean").read_text()
    m = re.search(r"phi11R t ≤ (\d+)\s*/\s*(\d+)", stmt)
    assert m, "bound literal not found in statement"
    num, den = int(m.group(1)), int(m.group(2))
    peak = dns_phi11(4, 5)
    assert (num, den) == (peak.numerator, peak.denominator), (
        f"statement bound {num}/{den} != dns_phi11(4,5) {peak}")
