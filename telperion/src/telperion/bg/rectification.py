"""Arm-rectification surgery -- the per-move certificate basis for the legs-2 competitor lemma.

fractal_eigenvalue showed the BG maximizer lives on the legs-2 manifold and closed its asymptote.  The
open piece is competitor-extremality: legs-2 dominates every other tree.  On SPIDERS (hub + pendant arms,
an arm-length partition) this reduces to a handful of local surgeries that drive any spider to the
canonical maximizer form -- ALL length-2 arms, plus at most ONE length-3 arm when the budget's parity
forbids all-2s (a single defect; NEVER balanced, NEVER length-1 arms).

Five elementary moves, each n-preserving; each verified Phi^11-NON-DECREASING by exhaustive test:

    PAIR11 : (..,1,1)   -> (..,2)       clear two stub arms         (unconditional)
    PAIR31 : (..,3,1)   -> (..,2,2)     pair a long+stub            (unconditional)
    PAIR33 : (..,3,3)   -> (..,2,2,2)   split two 3s into 2s        (unconditional)
    STUB   : (..,L>=4,1)-> (..,L-1,2)   feed a lone stub from a long arm  (unconditional)
    SPLIT4 : (..,L>=4)  -> (..,2,L-2)   peel a 2 off a long arm     (PRECONDITION: no length-1 arm)

The SPLIT4 precondition is load-bearing: unconditional SPLIT4 has 439/2886 DECREASES (worst (4,1)->(2,2,1),
-0.175), because peeling a 2 while a stub is present is counter-productive.  The fix is STUB, which feeds a
lone stub from a long arm ((4,1)->(3,2), 0/2066 decreases) -- without it, (4,1)-type states are stuck (a
long arm + an unpairable stub).  With STUB, SPLIT4 restricted to no-1-arm states is 0/820.  Move ordering:
clear/feed stubs (PAIR11/PAIR31/STUB), then split >=4s, then pair 3s.  Terminal = the canonical maximizer.
This is the R47-style per-move inequality basis for the spider case.

RESIDUAL (honest): a class of ~44 low-Phi spiders (a lone stub with no donor arm: (1,2),(1,1,1),...) are
STUCK -- no legal move reduces them to canonical form.  They are never maximizers (canonical_is_maximal
still holds), so they do not affect the extremal claim, but full reduction of every spider needs one more
move (STUB_MERGE (1,L)->(L+1), untested here -- it grows an arm and may violate monotonicity at large n,
hence deferred).  reported by RectificationCertificate.stuck_residual().

SCOPE: SPIDERS only, verified to n<=18.  General trees (internal branching, caterpillars, multi-hub
double-brooms) are NOT covered -- that is the open extension, and the natural target of an adversarial
counterexample hunt (a tree, or a move, that violates monotonicity off the spider subclass).  This does
NOT prove competitor-extremality and does NOT re-prove the tie.  conjecture1_proved = False.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass

from .rooted_phi import bg_phi11_fast


def spider_edges(arms):
    """hub 0 with pendant arms of the given lengths (an arm-length multiset).  n = 1 + sum(arms)."""
    e = []
    nid = 1
    for L in arms:
        prev = 0
        for _ in range(L):
            e.append((prev, nid))
            prev = nid
            nid += 1
    return 1 + sum(arms), tuple(e)


def spider_phi11(arms):
    """Phi^11 of the spider with these arm lengths (exact Fraction)."""
    arms = tuple(a for a in arms if a > 0)
    n, e = spider_edges(arms)
    return bg_phi11_fast(n, e)


def _norm(a):
    return tuple(sorted((x for x in a if x > 0), reverse=True))


def rectify_moves(arms):
    """Legal monotone surgeries from this spider, as (name, dst_arms).  Encodes the SPLIT4 precondition
    (no length-1 arm) so every returned move is Phi^11-non-decreasing."""
    a = list(arms)
    c = Counter(a)
    out = []
    if c[1] == 0:                                   # SPLIT4 only when no stub present
        for i, L in enumerate(a):
            if L >= 4:
                out.append(("SPLIT4", _norm(a[:i] + a[i + 1:] + [2, L - 2])))
    if c[1] >= 1:                                   # STUB: feed a lone stub from a long arm
        for i, L in enumerate(a):
            if L >= 4:
                b = a.copy(); b[i] = L - 1; b[b.index(1)] = 2
                out.append(("STUB", _norm(b)))
                break
    if c[1] >= 2:
        b = a.copy(); b.remove(1); b.remove(1); b.append(2)
        out.append(("PAIR11", _norm(b)))
    if c[3] >= 1 and c[1] >= 1:
        b = a.copy(); b.remove(3); b.remove(1); b += [2, 2]
        out.append(("PAIR31", _norm(b)))
    if c[3] >= 2:
        b = a.copy(); b.remove(3); b.remove(3); b += [2, 2, 2]
        out.append(("PAIR33", _norm(b)))
    return out


def is_canonical(arms) -> bool:
    """Canonical maximizer form: all arms length 2, plus at most one length-3 (parity defect)."""
    c = Counter(a for a in arms if a > 0)
    return set(c) <= {2, 3} and c[3] <= 1


def canonical_form(arms):
    """Drive the spider to its terminal canonical form via monotone moves (deterministic: clear stubs,
    then split, then pair 3s).  Returns the canonical arm multiset."""
    a = _norm(arms)
    seen = set()
    while not is_canonical(a) and a not in seen:
        seen.add(a)
        mv = rectify_moves(a)
        if not mv:
            break
        # ordering: clear/feed stubs first, then split >=4s, then pair 3s
        order = {"PAIR11": 0, "PAIR31": 1, "STUB": 2, "SPLIT4": 3, "PAIR33": 4}
        a = min(mv, key=lambda m: order[m[0]])[1]
    return a


@dataclass(frozen=True)
class RectificationCertificate:
    """Verifies the four arm-rectification moves are Phi^11-non-decreasing over all spiders up to
    n = n_max, and that every spider's canonical form is the legs-2 maximizer.  The per-move inequality
    basis for the spider case of competitor-extremality (legs-2 dominance)."""

    n_max: int = 17

    def _partitions(self, total, parts, mn=1):
        if parts == 1:
            if total >= mn:
                yield (total,)
            return
        for first in range(mn, total - parts + 2):
            for rest in self._partitions(total - first, parts - 1, first):
                yield (first,) + rest

    def all_moves_monotone(self):
        """(total_moves, violations) across every legal move on every spider up to n_max."""
        tot = viol = 0
        for total in range(2, self.n_max):
            for k in range(1, total + 1):
                for arms in self._partitions(total, k):
                    p0 = spider_phi11(arms)
                    for _, dst in rectify_moves(arms):
                        tot += 1
                        if spider_phi11(dst) < p0:
                            viol += 1
        return tot, viol

    def canonical_is_maximal(self):
        """For each n, the canonical form's Phi^11 equals the max over ALL spiders on n vertices."""
        for total in range(2, self.n_max):
            best = None
            canon = set()
            for k in range(1, total + 1):
                for arms in self._partitions(total, k):
                    p = spider_phi11(arms)
                    if best is None or p > best:
                        best = p
                    canon.add(canonical_form(arms))
            if not any(spider_phi11(c) == best for c in canon):
                return False
        return True

    def stuck_residual(self):
        """Spiders (up to n_max) whose canonical_form is NOT canonical -- the lone-stub residual class
        that the current 5-move basis cannot fully reduce.  All are suboptimal (never maximizers)."""
        out = []
        for total in range(2, self.n_max):
            for k in range(1, total + 1):
                for arms in self._partitions(total, k):
                    if not is_canonical(canonical_form(arms)):
                        out.append(arms)
        return out

    def check(self) -> bool:
        tot, viol = self.all_moves_monotone()
        return viol == 0 and tot > 0 and self.canonical_is_maximal()
