"""Zero-free region certificates (Lee-Yang / Barvinok lens), compile-gated.

Certifies a partition-function-like polynomial is ZERO-FREE in a disk via the
Rouche dominant-constant-term bound |a0| > sum|ak|r^k; inside, log p is analytic
(Barvinok interpolation).  Avenue B: the tie as the nearest complex zero rather
than an optimum.  conjecture1_proved=False.
"""
from __future__ import annotations

import argparse
import sys
from fractions import Fraction as Fr
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "src"))

from telperion.bg import (  # noqa: E402
    GridSpec,
    InequalityFamily,
    LeanProfile,
    ValidationReport,
    ZeroFreeDiskCertificate,
    certify,
    diff_frozen,
    emit,
    freeze,
)
from telperion.emit_adapters import CustomAssemblyEmitter  # noqa: E402

HERE = Path(__file__).resolve().parent
CERTS = [
    ZeroFreeDiskCertificate("zerofree_disk_r2", (10, 1, 1), Fr(2)),
    ZeroFreeDiskCertificate("zerofree_disk_r3", (100, 3, 2, 1), Fr(3)),
]


def build():
    body = "\n".join(c.lean() for c in CERTS)
    em = CustomAssemblyEmitter(
        statement_template="«thms»«branches»", branch_template="",
        fills=lambda f: {"thms": body}, branch_fills=lambda i: {},
        theorems=len(CERTS))
    return emit(certify(_t()), LeanProfile(namespace=("G1", "ZeroFree")), [em],
                _v(), file_name="ZeroFree.lean")


def _t():
    return InequalityFamily(name="ZeroFree", symbols=(), grid=GridSpec([("i", [0])]),
                            lean_name=lambda p: "zerofree_root",
                            target=lambda p: sp.Integer(0))


def _v():
    def ok():
        assert all(c.check() for c in CERTS)
    return ValidationReport.from_asserts([("zerofree", ok)])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    res = build()
    if a.check:
        r = diff_frozen(res, HERE / "frozen")
        print("check:", "OK" if r.ok else "FAILED")
        return 0 if r.ok else 1
    freeze(res, HERE / "frozen")
    print(f"ZeroFree: {res.n_theorems} zero-free disk certs, hash {res.input_hash[:16]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
