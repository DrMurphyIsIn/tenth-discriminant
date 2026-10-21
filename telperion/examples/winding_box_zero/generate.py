"""Generate the winding-box-zero example: certify -> emit SIDECAR + doc stub.

    python examples/winding_box_zero/generate.py           # write the .cert.json + doc stub
    python examples/winding_box_zero/generate.py --check    # drift check (no write)

winding_box_zero is an ARB-TRUST-CLASS kind (the same trust class as turing_band's sidecars): the
rigorous winding-number zero count of an analytic function on a rational-cornered box.  It ships NO
kernel theorem — the emitter produces a ``.cert.json`` sidecar (box, edge-sample count, precision,
winding integer, ``trust_class="arb"``) and a documentation stub (a Lean COMMENT, no theorem) that
honestly states the trust boundary.

For a CI-runnable, libflint-free example, the winding is computed by a self-contained pure-Python
analytic double (the SAME quadrant-advance argument principle as `arb_dh.winding_number`) applied to
`f(z) = z − z₀`: a box enclosing `z₀` has winding 1, a box not enclosing it has winding 0.  In
production, `winding_fn` defaults to `arb_dh.winding_number` (rigorous Arb balls) — see the emitter
docstring.  conjecture1_proved = False.
"""
import argparse
import cmath
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion import (  # noqa: E402
    WindingBoxZeroEmitter, ValidationReport, certify, emit,
)
from telperion.emit_winding_box_zero import (  # noqa: E402
    winding_box_zero_family, register_winding_fn,
)
from telperion.family import GridSpec  # noqa: E402
from telperion.lean import LeanProfile  # noqa: E402

_OUT_STUB = Path(__file__).resolve().parent / "WindingBoxZero.cert.lean"
_OUT_JSON = Path(__file__).resolve().parent / "WindingBoxZero.cert.json"


def _analytic_winding_double(z0: complex):
    """A libflint-free rigorous-in-exact-float winding double: quadrant-advance argument principle
    for `f(z) = z − z0` around the boundary of `[re0,re1]×[im0,im1]`.  Mirrors arb_dh.winding_number
    (which uses Arb balls); for `z − z0` the float phase is exact enough away from the contour."""
    def _wind(re0, re1, im0, im1, prec, n_per_side):
        r0, r1, i0, i1 = map(float, (re0, re1, im0, im1))
        N = n_per_side
        pts = []
        for k in range(N):
            pts.append(complex(r0 + (r1 - r0) * k / N, i0))
        for k in range(N):
            pts.append(complex(r1, i0 + (i1 - i0) * k / N))
        for k in range(N):
            pts.append(complex(r1 - (r1 - r0) * k / N, i1))
        for k in range(N):
            pts.append(complex(r0, i1 - (i1 - i0) * k / N))
        total = 0.0
        for a in range(len(pts)):
            b = (a + 1) % len(pts)
            va, vb = pts[a] - z0, pts[b] - z0
            d = cmath.phase(vb) - cmath.phase(va)
            while d > cmath.pi:
                d -= 2 * cmath.pi
            while d < -cmath.pi:
                d += 2 * cmath.pi
            total += d
        return round(total / (2 * cmath.pi))
    return _wind


# Register the libflint-free double under a STABLE STRING name so the family spec is fully
# byte-serializable (a bare function in the spec would inject a memory address into the
# provenance input hash, making regeneration non-deterministic).
register_winding_fn("analytic_double_half", _analytic_winding_double(complex(0.5, 0.5)))

_SPECS = {
    0: {"re0": "0", "re1": "1", "im0": "0", "im1": "1", "expected_winding": 1,
        "prec": 64, "n_per_side": 32, "winding_fn": "analytic_double_half"},
    1: {"re0": "1", "re1": "2", "im0": "1", "im1": "2", "expected_winding": 0,
        "prec": 64, "n_per_side": 32, "winding_fn": "analytic_double_half"},
}
_NAMES = {0: "winding_zero_inside", 1: "winding_zero_outside"}


def build() -> tuple[str, list[dict]]:
    fam = winding_box_zero_family(
        "WindingBoxZero",
        GridSpec([("case", [0, 1])]),
        lambda pt: _NAMES[pt["case"]],
        spec=lambda pt: _SPECS[pt["case"]],
    )
    em = WindingBoxZeroEmitter()
    report = emit(
        certify(fam),
        LeanProfile(namespace=("WindingBoxZero",)),
        [em],
        ValidationReport(checks=(("winding_box_zero", True),)),
    )
    stub = next(iter(report.files.values()))
    return stub, em._cert_sink


def main(*, check: bool = False) -> int:
    stub, sidecars = build()
    sidecar_text = json.dumps(sidecars, indent=2, sort_keys=True) + "\n"
    if check:
        drift = False
        if not _OUT_STUB.exists() or _OUT_STUB.read_text(encoding="utf-8") != stub:
            print("DRIFT: WindingBoxZero.cert.lean does not match regeneration")
            drift = True
        if not _OUT_JSON.exists() or _OUT_JSON.read_text(encoding="utf-8") != sidecar_text:
            print("DRIFT: WindingBoxZero.cert.json does not match regeneration")
            drift = True
        if drift:
            return 1
        print("check: OK (sidecar + doc stub match regeneration byte-for-byte)")
        return 0
    _OUT_STUB.write_text(stub, encoding="utf-8")
    _OUT_JSON.write_text(sidecar_text, encoding="utf-8")
    print(f"wrote {_OUT_STUB} + {_OUT_JSON} ({len(sidecars)} Arb sidecar(s))")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    raise SystemExit(main(check=ap.parse_args().check))
