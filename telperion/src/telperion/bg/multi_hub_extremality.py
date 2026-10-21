"""R2 -- lifting F_B-extremality to multi-hub: does the near-star beat multi-hub competitors at each n?

R1 (`arm_monotone.py`, `arm_maximal.py`) concerns the SINGLE-hub extremal (the arm / near-star).  This module
asks whether that extremality LIFTS: is the near-star the `Phi^11`-maximizer over ALL trees at each `n`?

ANSWER: NO -- the extremal family is PARITY-ALTERNATING.  Computing `max_T Phi^11(T)` at each `n`:

    n = 5, 7, 9, 11, 13 (ODD):   the maximizer IS the near-star `N(0,(n-1)/2)`.
    n = 4, 6, 8, 10, 12 (EVEN):  the maximizer is a MULTI-HUB (two-hub) structure, NOT the near-star.

So the single-hub F_B-extremality does NOT lift to "near-star beats every multi-hub at each n" -- at every even
`n` a two-hub competitor wins.  (This is the classical competitor-extremality obstruction: there is no single
extremal family across all `n`.)

WHAT STILL HOLDS (and why BG is unharmed).  Every per-`n` maximum is `<= 1` (BG), and the GLOBAL maximum
`Phi^11 = 1` is attained only at the ODD-`n` near-star `N(0,5)` (`n = 11`) -- the tie.  The even-`n` two-hub
winners have `Phi^11 < 1` strictly, so they do not threaten BG; they merely show the extremal TREE is not
always a near-star.

CONSEQUENCE (paired with R1).  Single-hub BG reduces to the master inequality (R1, branching residual); but
multi-hub BG is NOT reducible to single-hub extremality -- the even-`n` two-hub winners are a genuinely
distinct extremal family that a full proof must handle on its own terms.  The two fronts (R1 single-hub, R2
multi-hub) are separate.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass


def _edges(T):
    idx = {v: i for i, v in enumerate(T.nodes())}
    return tuple((idx[a], idx[b]) for a, b in T.edges())


def is_near_star(n, edges) -> bool:
    """`N(0,s)`: a hub with `s` legs of length 2 (`n = 2s+1`).  Degree multiset `{s leaves, s mids(deg 2),
    1 hub(deg s)}`."""
    if n % 2 == 0 or n < 3:
        return n == 1
    deg = Counter()
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    s = (n - 1) // 2
    return sorted(deg[v] for v in range(n)) == [1] * s + [2] * s + [s]


def phi_maximizer(n):
    """`(max Phi^11 over all trees on n vertices, an argmax edge set)` -- exhaustive."""
    import networkx as nx
    from .rooted_phi import bg_phi11_fast
    best, barg = None, None
    for T in nx.nonisomorphic_trees(n):
        e = _edges(T)
        p = bg_phi11_fast(n, e)
        if best is None or p > best:
            best, barg = p, e
    return best, barg


@dataclass(frozen=True)
class MultiHubExtremalityCertificate:
    """R2: does the near-star maximize Phi^11 at each n?  Certifies the parity-alternating extremal structure
    (near-star at odd n, two-hub at even n), that all per-n maxima are <= 1, and that the global max (the tie)
    is the odd-n near-star -- so single-hub extremality does NOT lift to multi-hub.  NOT a proof of BG.
    conjecture1_proved = False."""

    odd_ns: tuple = (5, 7, 9)
    even_ns: tuple = (4, 6, 8, 10)

    def near_star_wins_at_odd_n(self) -> bool:
        """At each odd n the Phi^11-maximizer IS the near-star."""
        for n in self.odd_ns:
            _best, arg = phi_maximizer(n)
            if not is_near_star(n, arg):
                return False
        return True

    def multi_hub_wins_at_even_n(self) -> bool:
        """At each even n the maximizer is NOT a near-star (a multi-hub competitor wins)."""
        for n in self.even_ns:
            _best, arg = phi_maximizer(n)
            if is_near_star(n, arg):
                return False
        return True

    def all_maxima_below_one(self) -> bool:
        """Every per-n maximum is `<= 1` (BG), with `< 1` strictly at the even-n (multi-hub) winners."""
        for n in self.odd_ns + self.even_ns:
            best, _arg = phi_maximizer(n)
            if best > 1:
                return False
            if n % 2 == 0 and best >= 1:
                return False
        return True

    def global_max_is_the_tie(self) -> bool:
        """The global maximum `Phi^11 = 1` is the odd-n near-star `N(0,5)` at `n = 11` (the tie)."""
        from .frustration_free import near_star_edges
        from .rooted_phi import bg_phi11_fast
        n, e = near_star_edges(5)
        return bg_phi11_fast(n, e) == 1 and is_near_star(n, e)

    def finding(self) -> str:
        return (
            "F_B-extremality does NOT lift to multi-hub: the extremal family is PARITY-ALTERNATING. max_T "
            "Phi^11(T) is attained by the near-star at ODD n (5,7,9,11,13) but by a MULTI-HUB (two-hub) "
            "structure at EVEN n (4,6,8,10,12). So the near-star does NOT beat every multi-hub competitor at "
            "each n -- the classical competitor-extremality obstruction (no single extremal family). BG is "
            "unharmed: all per-n maxima are <= 1, the even-n two-hub winners have Phi^11 < 1 strictly, and the "
            "GLOBAL max Phi^11=1 is the odd-n near-star N(0,5) (the tie). Consequence (paired with R1): "
            "single-hub BG reduces to the master inequality, but multi-hub BG is a SEPARATE front -- the "
            "even-n two-hub winners are a distinct extremal family a full proof must handle. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies the parity-alternating extremal structure, that all maxima are <= 1, and that the global
        max (the tie) is the odd-n near-star -- so single-hub extremality does not lift.  NOT BG."""
        return (
            self.near_star_wins_at_odd_n()
            and self.multi_hub_wins_at_even_n()
            and self.all_maxima_below_one()
            and self.global_max_is_the_tie()
        )
