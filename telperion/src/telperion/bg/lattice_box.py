"""Dimensional-lift skill — the integer-Positivstellensatz in d dimensions.

The 1-D bridge (bridge.py) crosses a single-parameter family by finite integer
base + monotone SOS tail.  This lifts it to ℤ^d: certify f(x) <= bound for all
x in ℤ^d_{>=0} by

  (1) a finite BASE BOX  B = [0,N_1] x ... x [0,N_d]  (all integer points, exact),
      chosen to contain every continuous-relaxation violation;
  (2) a MONOTONE TAIL in each coordinate direction j: for x_j >= N_j, adding one
      to x_j does not increase f (f(x + e_j) <= f(x)) -- a 1-D SOS/ratio tail per
      direction.

Then any x in ℤ^d reduces to the box by stepping down each over-the-box coordinate
(monotone tails), landing on a base point (<= bound).  Structurally, the extremal
configuration lives on a LOW-DIMENSIONAL FACE (for the crux 2-D family the max is
on the k2=0 edge = the 1-D near-star), and the new directions only decrease f --
so the d-D certificate is the (d-1)-D certificate on the face plus one monotone
tail.  This is how the crossing extends 1-D -> 2-D -> general d for a FIXED,
FINITE set of child types.

HONEST SCOPE: the general crux has UNBOUNDED type-dimension (each distinct subtree
is a coordinate), so no fixed d closes it -- the tails must themselves be handled
by the recursion (the open telescoping).  This skill crosses every fixed-d family
and reduces the general problem to: a monotone tail certificate UNIFORM in the
recursively-generated directions.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


@dataclass(frozen=True)
class LatticeBoxCertificate:
    """f: ℤ^d_{>=0} -> ℚ certified <= bound via base box + per-direction monotone
    tails.  f_of(x) returns the exact rational value at an integer point x (tuple);
    box = (N_1,...,N_d); bound default 1."""

    name: str
    d: int
    f_of: Callable[[tuple], object]
    box: tuple
    bound: object = 1

    def base_points(self):
        import itertools
        ranges = [range(self.box[j] + 1) for j in range(self.d)]
        return list(itertools.product(*ranges))

    def base_holds(self) -> bool:
        return all(self.f_of(x) <= self.bound for x in self.base_points())

    def tail_monotone(self, j: int, reach: int = 6) -> bool:
        """f(x + e_j) <= f(x) for x_j >= N_j, sampled to `reach` beyond the box in
        direction j (with other coords swept across the box) -- the empirical
        witness that direction j has a monotone tail (a full proof needs the 1-D
        SOS tail certificate, as in bridge.py)."""
        import itertools
        others = [range(self.box[k] + 1) for k in range(self.d) if k != j]
        for rest in itertools.product(*others):
            for xj in range(self.box[j], self.box[j] + reach):
                x = list(rest[:j]) + [xj] + list(rest[j:]) if False else None
                x = self._insert(rest, j, xj)
                xp = self._insert(rest, j, xj + 1)
                if self.f_of(xp) > self.f_of(x):
                    return False
        return True

    def _insert(self, rest, j, xj):
        x = list(rest)
        x.insert(j, xj)
        return tuple(x)

    def check(self) -> bool:
        return self.base_holds() and all(self.tail_monotone(j) for j in range(self.d))

    def lean(self) -> str:
        from fractions import Fraction as Fr
        mx, argmax, pinned = self.extremal_face()
        lines = [
            f"-- {self.name}: dimensional-lift certificate in ℤ^{self.d}. f <= {self.bound}\n"
            f"-- on ℤ^{self.d}_{{>=0}} via finite base box {self.box} (all integer points,\n"
            f"-- exact) + a monotone tail in each of the {self.d} directions.  The max\n"
            f"-- lives on the face with coords {pinned} pinned to 0 -- the lower-D\n"
            f"-- extremizer (for the crux 2-D family: the 1-D near-star edge).\n"
        ]
        for i, x in enumerate(self.base_points()):
            v = Fr(self.f_of(x))
            xs = "_".join(str(t) for t in x)
            if v < self.bound:
                lines.append(f"theorem {self.name}_box_{xs} : "
                             f"({v.numerator}:ℚ) < {v.denominator} := by norm_num")
            else:  # equality at the tie
                lines.append(f"theorem {self.name}_box_{xs} : "
                             f"(({v.numerator}:ℚ)/{v.denominator}) = 1 := by norm_num")
        return "\n".join(lines) + "\n"

    def extremal_face(self):
        """The lowest-dimensional face carrying the max over the base box -- for
        the crux 2-D family this is the k2=0 edge (the 1-D near-star)."""
        pts = self.base_points()
        mx = max(self.f_of(x) for x in pts)
        argmax = [x for x in pts if self.f_of(x) == mx]
        # which coordinates are pinned to 0 across all maximizers -> the face
        pinned = tuple(j for j in range(self.d)
                       if all(x[j] == 0 for x in argmax))
        return mx, argmax, pinned
