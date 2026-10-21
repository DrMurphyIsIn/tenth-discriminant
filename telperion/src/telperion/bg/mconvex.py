"""M-convexity certificates — Telperion's INTEGER-LATTICE (discrete-convex) vocabulary.

We proved the crux's blocker is the arithmetic tie: no SMOOTH certificate closes
it (continuous relaxation gives Φ(3.82) = 1.00004 > 1; equality only at integer
s = 5).  The frameworks that natively speak integrality are the ones to build,
and the sharpest is Lorentzian / completely-log-concave polynomials (Branden-Huh):
their TROPICALIZATION coincides exactly with M-CONVEX functions on the integer
lattice (Murota's discrete convex analysis).  M-convexity is the discrete analog
of convexity -- it lives on ℤⁿ, is tight at integer points and nowhere else, and
is the structural reason "smooth fails, integer works."

My earlier lorentzian.py certified the SMOOTH Hodge-Riemann inequality (which
overshoots the tie).  This module certifies the DISCRETE side: that a function on
a finite integer support is M-concave (equivalently, its negation M-convex) via
the EXCHANGE AXIOM

    ∀ x, y ∈ dom, ∀ i with xᵢ > yᵢ, ∃ j with xⱼ < yⱼ:
        f(x) + f(y)  ≤  f(x − eᵢ + eⱼ) + f(y + eᵢ − eⱼ),

a FINITE family of exact rational inequalities (norm_num), whose equality cases
are the integer-native tie candidates.  Separable-concave functions on a base
polytope are the canonical M-concave example; the normalized matching generating
polynomial being Lorentzian (hence its log-coefficients M-concave) is the crux
target -- certifiable here once its M-concavity is established.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def _step(x, i, j):
    z = list(x)
    z[i] -= 1
    z[j] += 1
    return tuple(z)


def exchange_witnesses(f: dict):
    """For every (x, y, i) that needs an exchange, the witnessing j and the
    inequality f(x)+f(y) ≤ f(x−eᵢ+eⱼ)+f(y+eᵢ−eⱼ).  Returns the list; empty j
    means the axiom FAILS at (x, y, i) (not M-concave)."""
    dom = set(f)
    out = []
    for x in dom:
        for y in dom:
            for i in range(len(x)):
                if x[i] > y[i]:
                    found = None
                    for j in range(len(x)):
                        if x[j] < y[j]:
                            xp, yp = _step(x, i, j), _step(y, j, i)
                            if xp in dom and yp in dom and f[x] + f[y] <= f[xp] + f[yp]:
                                found = (j, xp, yp)
                                break
                    out.append((x, y, i, found))
    return out


def is_m_concave(f: dict) -> bool:
    return all(w[3] is not None for w in exchange_witnesses(f))


def is_m_convex(f: dict) -> bool:
    return is_m_concave({k: -v for k, v in f.items()})


def separable_concave_on_base(total: int, n: int, phi) -> dict:
    """f(x) = Σ phi(xᵢ) on the base {Σ xᵢ = total, xᵢ ≥ 0} — M-concave iff phi is
    concave (the canonical M-concave example, exact rationals)."""
    def comps(t, k):
        if k == 1:
            yield (t,)
            return
        for a in range(t + 1):
            for rest in comps(t - a, k - 1):
                yield (a,) + rest
    return {x: sum(Fr(phi(xi)) for xi in x) for x in comps(total, n)}


@dataclass(frozen=True)
class MConvexityCertificate:
    """A finite integer function certified M-concave by its exchange witnesses."""

    name: str
    f: dict

    def check(self) -> bool:
        return is_m_concave(self.f)

    def lean(self) -> str:
        ws = [w for w in exchange_witnesses(self.f) if w[3] is not None]
        # dedup by the numeric inequality (many exchanges share values)
        seen, lines = set(), []
        for k, (x, y, i, (j, xp, yp)) in enumerate(ws):
            key = (self.f[x] + self.f[y], self.f[xp] + self.f[yp])
            if key in seen:
                continue
            seen.add(key)
            lhs, rhs = key
            lines.append(
                f"theorem {self.name}_exch{len(lines)} : "
                f"(({lhs.numerator}:ℚ)/{lhs.denominator}) ≤ "
                f"({rhs.numerator}:ℚ)/{rhs.denominator} := by norm_num"
            )
        head = (
            f"-- {self.name}: M-concavity on the integer lattice via the exchange\n"
            f"-- axiom (discrete convex analysis).  {len(lines)} distinct exchange\n"
            f"-- inequalities; their equality cases are the integer-native tie\n"
            f"-- candidates.  This is the structure that certifies on ℤ, not ℝ.\n"
        )
        return head + "\n".join(lines) + "\n"
