"""Independent recomputation of the d <= 652 threshold with mpmath at 50 digits (float-level evidence; see arb_threshold.py for the
ball-arithmetic check).
zeta_K(s) for K = Q(sqrt(-d)), class number 1 assumed, so zeta_K = (1/2) Z_Q with Q the principal form (a=1):
  d = 3 mod 4: Q = x^2 + xy + (d+1)/4 y^2 (b = 1);   d = 0 mod 4: Q = x^2 + (d/4) y^2 (b = 0).
Chowla-Selberg (a = 1):
  zeta_K(s) = zeta(2s) + 2^{2s-1} sqrt(pi) Gamma(s-1/2)/Gamma(s) d^{1/2-s} zeta(2s-1)
            + 2^{s+3/2} pi^s /(Gamma(s) d^{s/2-1/4})   [prefactor 2^{s+3/2}; an earlier draft had 2^{s+1/2}, see computations/README.md] sum_n n^{s-1/2} sigma_{1-2s}(n) cos(n pi b) K_{s-1/2}(pi n sqrt d)
Cross-checked against direct lattice-sum continuation is NOT done here; a sanity check at s = 2 against the absolutely convergent
lattice sum is done instead. Reports the main term, the Bessel term, and the smallest d0 with zeta_K(7/8) > 0 for all d >= d0."""
import mpmath as mp
mp.mp.dps = 50
def sigma(n, a):
    return sum(mp.mpf(k)**a for k in range(1, n+1) if n % k == 0)
def zK(s, d, b, nmax=40):
    s = mp.mpf(s)
    main = mp.zeta(2*s) + 2**(2*s-1)*mp.sqrt(mp.pi)*mp.gamma(s-mp.mpf(1)/2)/mp.gamma(s)*mp.mpf(d)**(mp.mpf(1)/2-s)*mp.zeta(2*s-1)
    pref = 2**(s+mp.mpf(3)/2)*mp.pi**s/(mp.gamma(s)*mp.mpf(d)**(s/2-mp.mpf(1)/4))
    bess = pref*mp.fsum(mp.mpf(n)**(s-mp.mpf(1)/2)*sigma(n, 1-2*s)*mp.cos(n*mp.pi*b)*mp.besselk(s-mp.mpf(1)/2, mp.pi*n*mp.sqrt(d)) for n in range(1, nmax+1))
    return main, bess
# sanity at s = 2: compare with direct lattice sum (1/2) sum' Q^{-2}
def direct(s, d, b, R=400):
    c = (d + b*b)//4
    tot = mp.mpf(0)
    for x in range(-R, R+1):
        for y in range(-R, R+1):
            if x or y:
                tot += mp.mpf(x*x + b*x*y + c*y*y)**(-s)
    return tot/2
for d, b in [(163, 1), (67, 1), (4*41, 0)]:
    m, e = zK(2, d, b)
    print(f"sanity s=2 d={d}: CS {mp.nstr(m+e, 15)}  direct(R=400) {mp.nstr(direct(2, d, b), 15)}")
s = mp.mpf(7)/8
print("zeta(7/8) =", mp.nstr(mp.zeta(s), 12), " C = sqrt(pi)Gamma(3/8)/Gamma(7/8) =", mp.nstr(mp.sqrt(mp.pi)*mp.gamma(s-0.5)/mp.gamma(s), 12))
last_neg = None
for d in range(3, 3001):
    for b in ((1,) if d % 4 == 3 else (0,) if d % 4 == 0 else ()):
        m, e = zK(s, d, b, nmax=12)
        if m + e <= 0:
            last_neg = (d, b, m, e)
print("largest d <= 3000 with zeta_K(7/8) <= 0 (principal-form value):", last_neg[0], "b =", last_neg[1],
      "value", mp.nstr(last_neg[2] + last_neg[3], 8))
for d in [651, 652, 653, 654, 655, 659, 660, 663, 667]:
    b = 1 if d % 4 == 3 else 0 if d % 4 == 0 else None
    if b is None: continue
    m, e = zK(s, d, b)
    print(f"d={d} b={b}: main {mp.nstr(m,10)}  bessel {mp.nstr(e,6)}  total {mp.nstr(m+e,10)}")
