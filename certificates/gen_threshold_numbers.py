#!/usr/bin/env python3
"""Exact bracket data for Threshold.lean (M(655) - B0(655) > 0).
M(d) = zeta(7/4) + 2^(3/4) sqrt(pi) G d^(-3/8) zeta(3/4),  G = Gamma(3/8)/Gamma(7/8).
Inputs proved in Lean: zeta(7/4) in [1.96232, 1.9623202], zeta(3/4) in [-3.44129, -3.44128],
G in [2.1753, 2.1755], pi in (3.141592, 3.141593) (Mathlib pi_gt_d6/pi_lt_d6).
Here: brackets for 2^(3/4), 655^(-3/8) (integer root inequalities) and sqrt(pi) (squares), and the
resulting lower bound for M(655). Exact rationals."""
from fractions import Fraction as F
def iroot(x, q):
    if x < 2: return x
    r = 1 << ((x.bit_length() + q - 1) // q)
    while True:
        y = ((q - 1) * r + x // r**(q - 1)) // q
        if y >= r: break
        r = y
    while r**q > x: r -= 1
    while (r+1)**q <= x: r += 1
    return r
S = 10**8
# 2^(3/4): L^4 <= 2^3 S^4 <= U^4
X = 2**3 * S**4; L = iroot(X, 4); U = L + (0 if L**4 == X else 1)
assert L**4 <= X <= U**4
two34 = (L, U); print("2^(3/4) in [%d, %d]/10^8" % two34)
# 655^(-3/8): L^8 * 655^3 <= S^8 <= U^8 * 655^3
X = S**8 // 655**3; L = iroot(X, 8); U = L + (0 if L**8 * 655**3 == S**8 else 1)
assert L**8 * 655**3 <= S**8 <= U**8 * 655**3
d38 = (L, U); print("655^(-3/8) in [%d, %d]/10^8" % d38)
# sqrt(pi): (a/10^7)^2 < 3.141592 and 3.141593 < (b/10^7)^2
pi_lo, pi_hi = F(3141592, 10**6), F(3141593, 10**6)
a = 17724536; b = 17724540
assert F(a, 10**7)**2 < pi_lo and pi_hi < F(b, 10**7)**2, (float(F(a,10**7)**2), float(F(b,10**7)**2))
print("sqrt(pi) in (%d, %d)/10^7" % (a, b))
z74_lo, z74_hi = F(196232, 10**5), F(19623202, 10**7)
z34_lo, z34_hi = F(-344129, 10**5), F(-344128, 10**5)
G_lo, G_hi = F(21753, 10**4), F(21755, 10**4)
P_hi = F(two34[1], S) * F(b, 10**7) * G_hi * F(d38[1], S)
P_lo = F(two34[0], S) * F(a, 10**7) * G_lo * F(d38[0], S)
M_lo = z74_lo + P_hi * z34_lo
M_hi = z74_hi + P_lo * z34_hi
print("P in [%.8f, %.8f]" % (float(P_lo), float(P_hi)))
print("M(655) in [%.8f, %.8f]   (Arb: 0.0011379074)" % (float(M_lo), float(M_hi)))
# B0(655) <= 4 * pi^(7/8) * G * 1 * exp(-40) <= 4 * 3.15 * 2.1755 * 1e-17
B0_hi = 4 * F(315,100) * G_hi * F(1, 10**17)
print("B0(655) <= %.3e" % float(B0_hi))
print("M_lo - B0_hi = %.8f  > 0:" % float(M_lo - B0_hi), M_lo - B0_hi > 0)
# e^40 >= 2.7182818283^40 >= 10^17 ?
print("2.7182818283^40 >= 1e17:", F(27182818283, 10**10)**40 >= 10**17, float(F(27182818283, 10**10)**40))
# pi*sqrt(655)/2 >= 40 with pi > 3.141592, sqrt(655) > 25.5 (25.5^2 = 650.25)
print("3.141592*25.5/2 =", 3.141592*25.5/2)
