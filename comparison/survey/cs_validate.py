"""CMP-1 shared reduction, step 1 (lead, 2026-10-25): validate our Chowla-Selberg normalisation against direct lattice sums.

For a positive definite form Q = a x^2 + b x y + c y^2 with b^2 - 4ac = -d, the Epstein zeta Z_Q(s) = sum over (x, y) != (0, 0)
of Q(x, y)^(-s) satisfies, for every s (Chowla-Selberg; the formula under test):

  Z_Q(s) = 2 zeta(2s) a^(-s) + 2^(2s) a^(s-1) sqrt(pi) Gamma(s - 1/2)/Gamma(s) zeta(2s - 1) d^(1/2 - s)
           + 2^(s + 5/2) pi^s / (Gamma(s) a^(1/2) d^(s/2 - 1/4)) * sum_{n >= 1} n^(s - 1/2) sigma_{1-2s}(n) cos(n pi b / a) K_{s-1/2}(pi n sqrt(d) / a)

The Bessel coefficient is what bb's M1 (CN-1) corrected; this script decides it by comparison at s = 2 and s = 3/2, where the
lattice sum converges. With h = 1 and w = 2, zeta_K(s) = Z_Q(s)/2 for the principal form."""
import mpmath as mp
mp.mp.dps = 40
def sigma(n, t): return sum(mp.mpf(k) ** t for k in range(1, n + 1) if n % k == 0)
def cs(a, b, c, s, nmax=40):
    d = 4 * a * c - b * b
    s = mp.mpf(s)
    main = 2 * mp.zeta(2 * s) * mp.mpf(a) ** (-s) + 2 ** (2 * s) * mp.mpf(a) ** (s - 1) * mp.sqrt(mp.pi) * mp.gamma(s - 0.5) / mp.gamma(s) * mp.zeta(2 * s - 1) * mp.mpf(d) ** (0.5 - s)
    pref = 2 ** (s + mp.mpf(5) / 2) * mp.pi ** s / (mp.gamma(s) * mp.sqrt(a) * mp.mpf(d) ** (s / 2 - 0.25))
    bes = pref * mp.fsum(mp.mpf(n) ** (s - 0.5) * sigma(n, 1 - 2 * s) * mp.cos(n * mp.pi * b / a) * mp.besselk(s - 0.5, mp.pi * n * mp.sqrt(d) / a) for n in range(1, nmax))
    return main + bes, main, bes
def direct(a, b, c, s, R):
    # exact sum over |x|, |y| <= R plus a crude tail estimate is NOT used: we compare convergence in R instead
    tot = mp.mpf(0)
    for x in range(-R, R + 1):
        for y in range(-R, R + 1):
            if x or y: tot += mp.mpf(a * x * x + b * x * y + c * y * y) ** (-s)
    return tot
for (a, b, c) in [(1, 1, 2), (1, 1, 3), (1, 1, 5), (2, 1, 3), (1, 0, 5)]:
    d = 4 * a * c - b * b
    for s in (3, 2):
        v, m, e = cs(a, b, c, s)
        r1, r2 = direct(a, b, c, s, 150), direct(a, b, c, s, 300)
        print(f"Q=({a},{b},{c}) d={d} s={s}: CS={mp.nstr(v, 15)}  direct R=150 {mp.nstr(r1, 15)}  R=300 {mp.nstr(r2, 15)}  Bessel part {mp.nstr(e, 6)}")
