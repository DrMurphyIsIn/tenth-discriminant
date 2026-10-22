#!/usr/bin/env python3
"""Exact integer data for GammaRatio.lean (n = 8000, x1 = 3/8, x2 = 7/8).
Bohr-Mollerup brackets (GammaBounds.lean):
  n (n+3/8)^(-5/8) / n^(7/8) * P  <=  Gamma(3/8)/Gamma(7/8)  <=  n^(3/8) / (n (n+7/8)^(-1/8)) * P,
  P = prod_{k<n} (7/8+k)/(3/8+k) = A/B,  A = prod (8k+7), B = prod (8k+3).
We bracket the four rpow factors at scale S = 10^12 by integer root inequalities and print the
resulting decimal enclosure. Exact integer arithmetic only."""
from fractions import Fraction
import sys
sys.setrecursionlimit(10000)
n = 8000
S = 10**12
def iroot(x, q):
    """floor(x^(1/q)), exact: Newton iteration from above, then a final fix-up."""
    if x < 2: return x
    r = 1 << ((x.bit_length() + q - 1) // q)   # >= true root
    while True:
        y = ((q - 1) * r + x // r**(q - 1)) // q
        if y >= r: break
        r = y
    while r**q > x: r -= 1
    while (r+1)**q <= x: r += 1
    return r
# (a/b)^(-p/q) lower: L^q a^p <= b^p S^q
def rat_neg_lower(a, b, p, q):
    X = b**p * S**q // a**p
    L = iroot(X, q); assert L**q * a**p <= b**p * S**q; return L
# m^(p/q) upper: m^p S^q <= U^q
def nat_pos_upper(m, p, q):
    X = m**p * S**q
    U = iroot(X, q)
    if U**q < X: U += 1
    assert X <= U**q; return U
l1 = rat_neg_lower(8*n+3, 8, 5, 8)      # (n+3/8)^(-5/8) >= l1/S
u2 = nat_pos_upper(n, 7, 8)             # n^(7/8) <= u2/S
u3 = nat_pos_upper(n, 3, 8)             # n^(3/8) <= u3/S
l4 = rat_neg_lower(8*n+7, 8, 1, 8)      # (n+7/8)^(-1/8) >= l4/S
A = 1; B = 1
for k in range(n):
    A *= 8*k+7; B *= 8*k+3
print("l1 =", l1); print("u2 =", u2); print("u3 =", u3); print("l4 =", l4)
print("digits A, B:", len(str(A)), len(str(B)))
lo = Fraction(n*l1*A, u2*B)
hi = Fraction(u3*A, n*l4*B)
print(f"ratio in [{float(lo):.9f}, {float(hi):.9f}]  width {float(hi-lo):.3e}")
# candidate decimal statement bounds
LO = Fraction(21753, 10000); HI = Fraction(21755, 10000)
print("LO <= lo:", LO <= lo, " hi <= HI:", hi <= HI)
# the exact Nat inequalities the kernel will check:
#   LO_num * u2 * B <= 10^4 * n * l1 * A    and   10^4 * u3 * A <= HI_num * n * l4 * B
print("key1:", 21753 * u2 * B <= 10**4 * n * l1 * A)
print("key2:", 10**4 * u3 * A <= 21755 * n * l4 * B)
try:
    import mpmath
    mpmath.mp.dps = 30
    print("mpmath Gamma(3/8)/Gamma(7/8) =", mpmath.gamma(mpmath.mpf(3)/8)/mpmath.gamma(mpmath.mpf(7)/8))
except ImportError:
    pass
