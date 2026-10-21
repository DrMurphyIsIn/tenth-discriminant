"""Arithmetic height ledger + displacement-convexity checkers — the exact-engine
side of the two crux objects that have NO finite certificate (yet).

These are deliberately NOT certificate emitters.  The crux's missing tools are:

  (A) an ARITHMETIC Hodge-Riemann / local-global height inequality: each node
      contributes a local height, and the non-negativity of the GLOBAL height is
      exactly `D >= N` (i.e. Phi^11 <= 1), tight at the tie by Diophantine
      rigidity.  Combinatorial Hodge theory is analytic-signed; Arakelov height
      theory is arithmetic but not built for this collective tree coupling.  No
      framework does both -- so there is nothing finite to emit.

  (B) a measure-valued Lyapunov / displacement-convexity functional for the
      belief-propagation (cavity) recursion: convexity that respects the
      DISTRIBUTION of children, not their mean -- the object that would make the
      non-additive telescoping close.  Constructing one tight at the tie is open.

What Telperion CAN honestly provide is the exact-arithmetic INSTRUMENTATION to
probe candidates: compute the adelic height decomposition of a rational, verify
the product formula (the ledger's conservation law), and test displacement
(Wasserstein-geodesic) convexity of a candidate functional on finite child
measures.  A future proof would supply the closed form; these check it.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr

from ..padic import padic_val


def local_heights(q: Fr, primes) -> dict:
    """The adelic local heights of a positive rational q = N/D over the given
    finite prime set plus the archimedean place.  local_p = -v_p(q)*log p (the
    log p-adic absolute value); local_inf = log q.  The PRODUCT FORMULA says they
    sum to 0 over ALL places -- so over a FINITE prime set the residual is the
    log of the p-free part, exposing which primes carry the height."""
    heights = {}
    for p in primes:
        vp = 0
        n, d = q.numerator, q.denominator
        if n % p == 0:
            vp = padic_val(n, p)
        elif d % p == 0:
            vp = -padic_val(d, p)
        heights[p] = -vp * math.log(p)          # log |q|_p
    heights["inf"] = math.log(float(q))          # log |q|_infty
    return heights


def product_formula_residual(q: Fr, primes) -> float:
    """Sum of local heights over the archimedean place + the given primes.  Zero
    (up to the omitted primes) iff `primes` captures every prime dividing N*D --
    the ledger's conservation check.  A candidate arithmetic-height certificate
    must account for exactly this balance (dominant column need not be a single
    prime -- measured multi-prime, see the crux map)."""
    return sum(local_heights(q, primes).values())


def global_height_nonneg(q: Fr) -> bool:
    """The crux, stated as a height: the GLOBAL height (here just log q for the
    normalized Phi^11 = N/D) is >= 0 iff D >= N iff Phi^11 <= 1.  This is the
    fact a future arithmetic Hodge-Riemann relation must prove structurally; here
    we only CHECK it for a given q (the untrusted-engine dual)."""
    return q <= 1


# ---- displacement / Wasserstein-geodesic convexity (checker only) -----------


def wasserstein1(mu: list[tuple[Fr, Fr]], nu: list[tuple[Fr, Fr]]) -> Fr:
    """Exact W_1 between two finite measures on the rationals given as sorted
    (point, mass) lists of equal total mass, via the CDF (inverse-transport)
    formula for 1-D optimal transport."""
    pts = sorted(set([p for p, _ in mu] + [p for p, _ in nu]))
    def cdf(m, x):
        return sum(w for p, w in m if p <= x)
    total = Fr(0)
    prev = pts[0]
    for a, b in zip(pts, pts[1:]):
        total += abs(cdf(mu, a) - cdf(nu, a)) * (b - a)
    return total


def displacement_convex(functional, mu0, mu1, geodesic, steps: int = 4) -> bool:
    """Test whether `functional` is displacement-convex along the Wasserstein
    geodesic `geodesic(t)` from mu0 to mu1 (t in [0,1]): F(geodesic(t)) <=
    (1-t)F(mu0) + t F(mu1) for sampled t.  This is the property a cavity Lyapunov
    functional would need -- convexity respecting the child DISTRIBUTION, which
    (unlike mean-convexity) can see the N(11,11) collectivity.  A checker, not a
    certificate: a future proof supplies a functional that is provably
    displacement-convex AND tight at the tie."""
    f0, f1 = functional(mu0), functional(mu1)
    for k in range(1, steps):
        t = Fr(k, steps)
        chord = (1 - t) * f0 + t * f1
        if functional(geodesic(t)) > chord + Fr(1, 10**9):
            return False
    return True
