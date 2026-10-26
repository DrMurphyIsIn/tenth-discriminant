"""CMP-1 shared reduction R-CS, edge form (lead, 2026-10-25). For the half-plane rows (normal form sigma0).

Claim: if no L(s, chi_{-d}) has a zero with Re s > sigma0 (1/2 < sigma0 < 1), and h(-d) = 1 with d > 4 (w = 2), then d < d*(sigma0).
Proof outline (each step labelled):
 (1) PROVED (continuity): L(sigma0, chi) >= 0, since L is real on (sigma0, 1], nonzero there, and L(1, chi) > 0. zeta(sigma0) < 0,
     so zeta_K(sigma0) = zeta(sigma0) L(sigma0, chi) <= 0.
 (2) CS, normalisation VALIDATED in cs_validate.py (2^(s+3/2) for zeta_K = Z_Q/2): zeta_K(sigma0) = M(d) + E(d), with
     M(d) = zeta(2 s) + 2^(2s-1) sqrt(pi) Gamma(s-1/2)/Gamma(s) zeta(2s-1) d^(1/2-s) at s = sigma0, and
     |E(d)| <= B(d) = 2^(s+3/2) pi^s/(Gamma(s) d^(s/2-1/4)) * sum_n n^(s-1/2) * dfun(n) * K_{1/2}(pi n sqrt d), using
     |sigma_{1-2s}(n)| <= dfun(n) <= n (PROVED, 1-2s < 0) and K_nu <= K_{1/2} for 0 <= nu <= 1/2 (CITED, DLMF 10.37: for fixed x > 0, K_nu(x) increases in nu >= 0; K_{-nu} = K_nu; to be read at source).
     With K_{1/2}(x) = sqrt(pi/(2x)) e^(-x) and n^(s-1/2) * n * n^(-1/2) = n^s <= 2^(n-1):
     B(d) <= 2^(s+3/2) pi^s/(Gamma(s) d^(s/2-1/4)) * sqrt(pi/(2 pi sqrt d)) * e^(-x)/(1 - 2 e^(-x)), x = pi sqrt d.
 (3) zeta(2s-1) < 0, so M increases in d; B decreases in d. Hence if M(D) - B(D) > 0 then zeta_K(sigma0) > 0 for all d >= D,
     contradicting (1).
 (4) The root of M is closed-form: d_M = (-C zeta(2s-1)/zeta(2s))^(1/(s-1/2)), C = 2^(2s-1) sqrt(pi) Gamma(s-1/2)/Gamma(s).
     Certified here as an Arb ball; then M(ceil d_M) - B(ceil d_M) > 0 is certified, so D0 = ceil(d_M) - 1.
Also tabulates d_M(sigma) for sigma in [sigma0, 1), to show whether evaluating at the edge is optimal."""
from flint import arb, ctx
import sys
ctx.prec = 300
def C(s): return arb(2) ** (2 * s - 1) * arb.pi().sqrt() * (s - arb(1) / 2).gamma() / s.gamma()
def M(s, d): return (2 * s).zeta() + C(s) * (2 * s - 1).zeta() * arb(d) ** (arb(1) / 2 - s)
def B(s, d):
    x = arb.pi() * arb(d).sqrt()
    pref = arb(2) ** (s + arb(3) / 2) * arb.pi() ** s / (s.gamma() * arb(d) ** (s / 2 - arb(1) / 4))
    return pref * (arb.pi() / (2 * x)).sqrt() * (-x).exp() / (1 - 2 * (-x).exp())
def dM(s): return (-C(s) * (2 * s - 1).zeta() / (2 * s).zeta()) ** (1 / (s - arb(1) / 2))
for num, den in [(7, 8), (11, 12)]:
    s = arb(num) / den
    r = dM(s)
    D = int(r.upper().floor().unique_fmpz()) + 1   # ceil of the ball
    m, b = M(s, D), B(s, D)
    ok = (m - b) > 0
    mprev = M(s, D - 1)
    print(f"sigma0 = {num}/{den}: d_M = {r.str(20)}; at D = {D}: M = {m.str(8)}, B <= {b.str(4)}, M - B > 0: {ok}; M(D-1) < 0: {mprev < 0}")
    print(f"   => h = 1, d > 4 implies d <= {D - 1}")
    for k in range(0, 9):
        t = s + (1 - s) * arb(k) / 10
        print(f"   sigma = {t.str(6)}: d_M = {dM(t).str(10)}")
