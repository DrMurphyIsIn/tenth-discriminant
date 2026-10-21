"""Forward-difference telescoping certificates (the W2 prover), compile-gated.

Mechanizes the SumEqProd.lean template: for f(q+1) = f(q)*A(q)/(P-q), the
closed form Delta^[j] f(q) = (-1)^j prod N * f(q) / prod (P-q-u) is certified
by ONE polynomial identity (the contiguous relation A(q)-(P-q-j)+N(j) = 0)
and emitted as the full Lean induction.

Demonstration: the Grigoriev knapsack pseudo-moment sequence (A = n/2 - q,
P = n, N = n/2 - u) — a RE-DERIVATION of the hand-proved SumEqProd.lean
core, now emitter-generated (verdict: re_derivation, by design: the worked
template is the regression baseline).
NEGATIVE CONTROL: a wrong numerator factor N fails the contiguous identity.
Usage: generate.py [--check]
"""
from __future__ import annotations
import argparse, sys
from pathlib import Path
import sympy as sp
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))
from telperion import (CertificationError, FwdTelescopeEmitter, GridSpec, LeanProfile,
    ValidationReport, certify, diff_frozen, emit, freeze, fwd_telescope_family)
HERE = Path(__file__).resolve().parent
n, q, u = sp.symbols("n q u")
def _family():
    return fwd_telescope_family("FwdTelescope", GridSpec([("i", [0])]),
        lambda pt: "knapsack_fwd_telescope",
        lambda pt: {"A": n / 2 - q, "P": n, "N": n / 2 - u})
def build():
    return emit(certify(_family()), LeanProfile(namespace=("G1", "FwdTelescope")),
        [FwdTelescopeEmitter()], _validation(), file_name="FwdTelescope.lean")
def _validation():
    def wrong_N_refused():
        bad = fwd_telescope_family("Bad", GridSpec([("i", [0])]), lambda pt: "bad",
            lambda pt: {"A": n / 2 - q, "P": n, "N": n / 2 - 2 * u})
        try: certify(bad); raise AssertionError("wrong N not refused")
        except CertificationError: pass
    return ValidationReport.from_asserts([
        ("contiguous_identity_discriminates", wrong_N_refused)])
def main():
    ap = argparse.ArgumentParser(); ap.add_argument("--check", action="store_true")
    a = ap.parse_args(); res = build()
    if a.check:
        rep = diff_frozen(res, HERE / "frozen"); print("check:", "OK" if rep.ok else "FAILED")
        if not rep.ok: print(*rep.details, sep="\n  ")
        return 0 if rep.ok else 1
    freeze(res, HERE / "frozen"); print(f"FwdTelescope: {res.n_theorems} certs, hash {res.input_hash[:16]}"); return 0
if __name__ == "__main__": sys.exit(main())
