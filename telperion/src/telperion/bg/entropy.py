"""Entropy-method certificates — Telperion's information-theoretic, degree-normalized lens.

Avenue C: Bregman's theorem bounds the permanent of a 0-1 matrix by
Π_v (d_v!)^(1/d_v) -- a bound NATIVELY normalized by degree, matching the ∏deg
denominator on the nose.  The entropy method proves it by writing the log-count
as a sum of per-vertex conditional entropies, with equality iff an independence
condition holds -- a clean equality characterization, a candidate for the tie.
An independent cross-check on A (Lorentzian) and B (zero-free): if it agrees, real.

The Bregman bound is irrational ((d!)^(1/d)), but it CLEARS to an exact integer
inequality by raising to L = lcm(d_v):

    per(A)^L  ≤  Π_v (d_v!)^(L/d_v),

both sides integers -- a rational certificate (norm_num).  Telperion had no
entropy / permanent-bound tooling; this adds the degree-normalized bound and the
Shearer sub-additivity checker whose equality case is the tie candidate.
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction as Fr
from itertools import permutations


def permanent01(A) -> int:
    n = len(A)
    total = 0
    for pi in permutations(range(n)):
        pr = 1
        for i in range(n):
            pr *= A[i][pi[i]]
            if pr == 0:
                break
        total += pr
    return total


def degrees(A):
    return [sum(row) for row in A]


def bregman_bound(A) -> float:
    b = 1.0
    for d in degrees(A):
        b *= math.factorial(d) ** (1.0 / d) if d else 1.0
    return b


@dataclass(frozen=True)
class BregmanCertificate:
    """per(A) ≤ Π (d_v!)^(1/d_v), cleared to the exact integer inequality
    per(A)^L ≤ Π (d_v!)^(L/d_v), L = lcm(d_v)."""

    name: str
    A: tuple

    def _cleared(self):
        ds = [d for d in degrees(self.A) if d > 0]
        L = math.lcm(*ds) if ds else 1
        lhs = permanent01(self.A) ** L
        rhs = 1
        for d in degrees(self.A):
            if d > 0:
                rhs *= math.factorial(d) ** (L // d)
        return lhs, rhs, L

    def check(self) -> bool:
        lhs, rhs, _ = self._cleared()
        return lhs <= rhs

    def lean(self) -> str:
        lhs, rhs, L = self._cleared()
        per = permanent01(self.A)
        ds = degrees(self.A)
        rhs_str = " * ".join(
            f"({math.factorial(d)})^{L // d}" for d in ds if d > 0
        ) or "1"
        return (
            f"-- {self.name}: Bregman permanent bound per(A) ≤ Π(d_v!)^(1/d_v),\n"
            f"-- cleared to integers (^L, L = lcm(d_v) = {L}); degree-normalized,\n"
            f"-- equality iff the entropy independence condition (the tie candidate).\n"
            f"-- per(A) = {per}, degrees = {ds}.\n"
            f"theorem {self.name} : (({per}:ℕ)^{L}) ≤ {rhs_str} := by norm_num\n"
        )


def shearer_holds(H, cover) -> bool:
    """Shearer sub-additivity check: H(full) ≤ (1/t) Σ_{S in cover} H(S), where
    every element is covered t times.  H is a dict {frozenset: entropy}.  The
    equality case is where the covered marginals are independent -- a tie
    candidate.  (Checker; a future proof supplies the exact entropy functional.)"""
    ground = max(cover, key=len)
    t = min(sum(1 for S in cover if e in S) for e in ground)
    return H[frozenset(ground)] <= Fr(1, t) * sum(H[frozenset(S)] for S in cover)
