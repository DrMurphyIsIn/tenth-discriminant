"""CMP-1 exploratory (lead, 2026-10-25; NUMERICAL, not certified). Does the CS main term M(s, d) have complex zeros with
Re s > 7/8 for d < 654? If so, 7/8 would exclude more d. Argument principle (mpmath, 30 digits, 2000 steps per side) on
[s0, 1.5] x [0.01, 40]. Result: 0 zeros for d in {300, 500, 570, 640, 700}, for s0 = 0.875 and 0.80. A NEGATIVE exploratory result."""
import mpmath as mp
mp.mp.dps = 30
def M(s, d):
    C = 2 ** (2 * s - 1) * mp.sqrt(mp.pi) * mp.gamma(s - 0.5) / mp.gamma(s)
    return mp.zeta(2 * s) + C * mp.zeta(2 * s - 1) * mp.mpf(d) ** (0.5 - s)
def count(d, s0, s1, T, n=2000):
    # argument principle on the rectangle [s0, s1] x [0.01, T] (avoids the real axis and the pole at s = 1 only if s1 < 1;
    # here the rectangle spans s = 1 + it, t >= 0.01, so the pole at t = 0 is excluded)
    path = [mp.mpc(s0, 0.01) + (s1 - s0) * k / n for k in range(n)] + \
           [mp.mpc(s1, 0.01 + (T - 0.01) * k / n) for k in range(n)] + \
           [mp.mpc(s1 - (s1 - s0) * k / n, T) for k in range(n)] + \
           [mp.mpc(s0, T - (T - 0.01) * k / n) for k in range(n + 1)]
    tot = 0; prev = M(path[0], d)
    for z in path[1:]:
        cur = M(z, d); tot += mp.arg(cur / prev); prev = cur
    return tot / (2 * mp.pi)
for d in (300, 500, 570, 640, 700):
    for (s0, s1, T) in [(0.875, 1.5, 40), (0.80, 1.5, 40)]:
        print(d, (s0, s1, T), "zeros of M in box (upper half, t > 0.01):", mp.nstr(count(d, s0, s1, T), 6))
