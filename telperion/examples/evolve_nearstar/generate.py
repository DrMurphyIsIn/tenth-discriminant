"""Freeze the evolve-discovered near-star champion into Lean.

Runs the structured (LLM-free) evolve loop (deterministic, seed=0), takes the
certifying champion, and writes its reusable ratio certificate — bundled with the
`Telperion.unimodal_peak` prelude — to `lean/EvolveNearStar.lean`.

    python examples/evolve_nearstar/generate.py           # (re)write the file
    python examples/evolve_nearstar/generate.py --check    # drift check (no write)

Idempotent: same seed → byte-identical output.
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.evolve.freeze import build_frozen_lean, discover_nearstar_champion  # noqa: E402

_OUT = Path(__file__).resolve().parent / "lean" / "EvolveNearStar.lean"


def main(*, check: bool = False) -> int:
    rep = discover_nearstar_champion(seed=0)
    c = rep.champion
    text = build_frozen_lean(c)
    if check:
        if not _OUT.exists() or _OUT.read_text(encoding="utf-8") != text:
            print("DRIFT: EvolveNearStar.lean does not match regeneration (seed=0)")
            return 1
        print("check: OK (regeneration matches frozen output byte-for-byte)")
        return 0
    print(
        f"champion: ratio_src={c.ratio_src} s0={c.s0} lift_max={c.lift_max} "
        f"score={rep.champion_score} evals={rep.evaluations}"
    )
    _OUT.parent.mkdir(exist_ok=True)
    _OUT.write_text(text, encoding="utf-8")
    print(f"wrote {_OUT} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="drift check; do not write")
    args = ap.parse_args()
    raise SystemExit(main(check=args.check))
