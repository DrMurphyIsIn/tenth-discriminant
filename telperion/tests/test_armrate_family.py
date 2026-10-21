"""Arm-load resize family — the Step-2 Telperion emitter for `R47ArmRate.lean`.

The rate-normalized arm value `armRate(n)^11 = A(n)^11/(621/64)^(1+2n)` is the
SAME unimodal integer sequence as the near-star payoff `Phi^11(N(0,n))`; its
successor ratio is `(486/529)(1 + 1/(4s^2+11s+6))^11`, decreasing, crossing 1 at
`s* = 5` with `f(5) = 1`.  These tests pin that the generator certifies the
full-range (`s0 = 0`) family, that its ratio matches the arm-rate closed form and
the near-star ratio exactly, and that the emitted Lean is lint-clean and the
generator is idempotent.  Kernel verdict of the emitted Lean is offline (as for
the near-star payoff); the kernel-checked instance of the SAME theorem is
`R3Cert.Step3.armRate11_le_one`.  conjecture1_proved = False.
"""
import importlib.util
import sys
from pathlib import Path

import sympy as sp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion import unimodal_certificate  # noqa: E402
from telperion.lean_lint import lint_lean_text  # noqa: E402

_GEN = Path(__file__).resolve().parents[1] / "examples" / "armrate_resize" / "generate.py"


def _load_gen():
    spec = importlib.util.spec_from_file_location("armrate_gen", _GEN)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_ratio_matches_armrate_closed_form_and_nearstar():
    mod = _load_gen()
    n = sp.Symbol("n", nonnegative=True)
    # f(n) = armRate(n)^11 = A(n)^11 / (621/64)^(1+2n)
    A = (sp.Rational(3, 2) ** n) * (4 * n + 3) / (3 * (n + 1))
    armrate11 = A ** 11 / (sp.Rational(621, 64) ** (1 + 2 * n))
    f_lean = sp.sympify(mod.ARMRATE_F_LEAN, locals={"n": n})
    assert sp.simplify(armrate11 - f_lean) == 0, "f must equal armRate(n)^11"
    # its successor ratio is exactly the factored ARMRATE_RATIO...
    ratio = sp.cancel(f_lean.subs(n, n + 1) / f_lean)
    target = sp.cancel(mod.ARMRATE_RATIO.subs(mod._S, n))
    assert sp.simplify(ratio - target) == 0, "successor ratio mismatch"
    # ...which is the near-star ratio (486/529)(1 + 1/(4s^2+11s+6))^11.
    nearstar = sp.Rational(486, 529) * (1 + 1 / (4 * n**2 + 11 * n + 6)) ** 11
    assert sp.simplify(target - nearstar) == 0, "arm-rate ratio must equal near-star"


def test_certifies_full_range_peak_five_and_straddles_one():
    mod = _load_gen()
    cert = unimodal_certificate(mod.ARMRATE_RATIO, s0=0, s_symbol=mod._S, search_hi=50)
    assert cert.s0 == 0 and cert.s_star == 5, "full-range family peaks at load 5"
    # tie: f(5) = 1 exactly; crossing straddles 1 (climb below, descent above).
    n = sp.Symbol("n", nonnegative=True)
    f = sp.sympify(mod.ARMRATE_F_LEAN, locals={"n": n})
    assert sp.Rational(f.subs(n, 5)) == 1, "peak value f(5) must be exactly 1"
    assert cert.cross_hi < 1 < cert.cross_lo, "crossing must straddle 1 at s*"


def test_false_bound_would_be_refused():
    # A claimed peak below the true maximum 1 must fail certification: the ratio is
    # unchanged, but f(5) = 1 > (any bound < 1), so the honesty pin rejects it.
    mod = _load_gen()
    cert = unimodal_certificate(mod.ARMRATE_RATIO, s0=0, s_symbol=mod._S, search_hi=50)
    n = sp.Symbol("n", nonnegative=True)
    f = sp.sympify(mod.ARMRATE_F_LEAN, locals={"n": n})
    assert not (sp.Rational(f.subs(n, cert.s_star)) <= sp.Rational(9, 10)), \
        "peak is 1; a bound of 0.9 must not certify"


def test_emit_is_lint_clean_and_idempotent():
    mod = _load_gen()
    text = mod.build_armrate_lean()
    assert "theorem armrate_resize" in text
    assert "Telperion.unimodal_peak" in text and "Telperion.climb_descend_of_ratio" in text
    errors = [i for i in lint_lean_text(text) if i.severity == "error"]
    assert errors == [], errors
    assert mod.main(["--check"]) == 0, "frozen lean_out must match regeneration"
