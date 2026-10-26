"""CMP-1 shared reduction R-CS, zero-forcing form (lead, 2026-10-25). For the zero-repulsion rows (normal form (c, q0)).

Credit: the zero-forcing route and its asymptotic constant kappa -> 6/pi are michaelmross's (Tao thread comment 698466,
repo michaelmross/tenth-discriminant 8b93bd20: 1 - beta < 2/sqrt d for d >= 1e10). This module re-derives it independently.

Lemma Z(kappa, d1): if h(-d) = 1, d >= d1 >= 100 (w = 2), then L(s, chi_{-d}) has a real zero beta with 1 - beta < kappa/sqrt(d).
Proof outline, with t = kappa/sqrt(d) and sigma = 1 - t (labels as in rcs_edge.py):
 (a) CS (validated normalisation): zeta_K(sigma) = M + E, M = zeta(2 sigma) + C(sigma) zeta(2 sigma - 1) d^(1/2 - sigma).
 (b) PROVED: zeta(2 - 2t) >= zeta(2), since zeta decreases on (1, oo).
 (c) PROVED (first-order Euler-Maclaurin): for real 0 < u < 1, zeta(u) = 1/(u-1) + 1/2 - u * I(u), with
     I(u) = int_1^oo ({x} - 1/2) x^(-u-1) dx < 0 (on each [k, k+1], {x} - 1/2 has mean 0 against a decreasing weight).
     So zeta(1 - 2t) > -1/(2t) + 1/2 > -1/(2t).
 (d) Hence M > zeta(2) - C(sigma) d^(-1/2) d^t/(2t) = zeta(2) - C(sigma) e^(t log d)/(2 kappa), and
     t log d = kappa log(d)/sqrt(d) <= kappa log(d1)/sqrt(d1) =: eps for d >= d1 (log x/sqrt x decreases for x > e^2).
     C(sigma) <= Cbar := sup of C over sigma in [1 - kappa/sqrt(d1), 1], enclosed by evaluating C on an Arb ball.
 (e) |E| <= Bbar, the bound of rcs_edge.py step (2) (valid: nu = sigma - 1/2 in [0, 1/2]; 1 - 2 sigma < 0; DLMF 10.37 as in rcs_edge.py), maximised over
     the same sigma-ball at d = d1, since it decreases in d.
 (f) If zeta(2) - Cbar e^eps/(2 kappa) - Bbar > 0, then zeta_K(sigma) > 0. But zeta_K(x) -> -oo as x -> 1- (simple pole with
     positive residue), so zeta_K has a zero in (sigma, 1). zeta has no zero in (0, 1), so L(beta, chi) = 0 for some
     beta in (sigma, 1), i.e. 1 - beta < kappa/sqrt(d).
Then, for a row with normal form (c, q0) (no real zero with (1 - beta) log q < c for q >= q0), at conductor q = d >= q0:
 (1 - beta) log d < kappa log(d)/sqrt(d) <= kappa log(q0)/sqrt(q0). If that is < c, then no class-number-one d >= q0, so D0 = q0
 (d < q0). Otherwise D0 is the d where kappa log d/sqrt d = c."""
from flint import arb, ctx
ctx.prec = 300
def C(s): return arb(2) ** (2 * s - 1) * arb.pi().sqrt() * (s - arb(1) / 2).gamma() / s.gamma()
def Bbar(s, d):
    x = arb.pi() * arb(d).sqrt()
    pref = arb(2) ** (s + arb(3) / 2) * arb.pi() ** s / (s.gamma() * arb(d) ** (s / 2 - arb(1) / 4))
    return pref * (arb.pi() / (2 * x)).sqrt() * (-x).exp() / (1 - 2 * (-x).exp())
NSUB = 256                                    # bb Z1: subdivide the sigma-ball; one ball over-encloses C
def lemma_ok(kappa, d1):
    kappa, d1a = arb(kappa), arb(d1)
    T = kappa / d1a.sqrt()
    tball = arb(T / 2, T / 2)                 # the ball [0, T]
    sig = 1 - tball
    Cbar = max((C(1 - arb(T * (2 * k + 1) / (2 * NSUB), T / (2 * NSUB)))).upper() for k in range(NSUB))
    eps = kappa * d1a.log() / d1a.sqrt()
    bb = Bbar(sig, d1).upper()
    lhs = arb(2).zeta() - arb(Cbar) * eps.exp() / (2 * kappa) - arb(bb)
    return lhs > 0, lhs
print("6/pi =", (6 / arb.pi()).str(12))
for d1 in (10**4, 10**6, 10**10):
    for kappa in ("1.92", "1.95", "2", "2.5"):
        ok, lhs = lemma_ok(arb(kappa), d1)
        print(f"d1 = {d1:.0e}, kappa = {kappa}: margin {lhs.str(8)}  OK: {ok}")
def D0(c, q0, kappa, d1):
    ok, _ = lemma_ok(kappa, d1); assert ok and d1 <= q0
    k, q = arb(kappa), arb(q0)
    v = k * q.log() / q.sqrt()
    return v, (v < c)
for name, c, q0 in [("Banks Thm 1.1", arb(3) / 1000, arb(10) ** 10), ("Kimura Thm 1, second part", arb(1193) / 200000, (arb(350131) / 10000).exp())]:
    kap = "1.95"
    v, ok = D0(c, q0, kap, 10**10)
    print(f"{name}: c = {c.str(6)}, q0 = {q0.str(8)}: kappa log q0/sqrt q0 = {v.str(6)} < c: {ok}  => D0 = q0 (d < q0); margin c/value = {(c / v).str(4)}")

# bb Z2: Kimura Thm 1 FIRST part, (1 - beta) log q >= 5811e-7 for all q >= 3 (kimura_2610.21511v2.txt:86-87), normal form
# (5811e-7, 3): here c binds. D0 = least d1 (on a grid) such that Lemma Z(kappa, d1) holds and kappa log d1/sqrt d1 < c; then
# every d >= d1 is excluded (log x/sqrt x decreases), so h = 1 implies d < d1.
def certify_c_binding(c, kappas, d1s):
    for d1 in d1s:
        for k in kappas:
            ok, m = lemma_ok(arb(k), d1)
            v = arb(k) * arb(d1).log() / arb(d1).sqrt()
            if ok and v < c:
                return d1, k, m, v
    return None
c1 = arb(5811) / 10**7
grid = [int(x * 10**9) for x in (4.0, 4.5, 5.0, 5.25, 5.5, 5.75, 6.0, 7.0, 8.0)]
r = certify_c_binding(c1, ["1.9105", "1.911", "1.912", "1.915", "1.92"], grid)
if r:
    d1, k, m, v = r
    print(f"Kimura Thm 1, first part: c = {c1.str(6)}: certified at d1 = {d1:.4e}, kappa = {k} (lemma margin {m.str(5)}), kappa log d1/sqrt d1 = {v.str(6)} < c  => D0: d < {d1:.4e}")
print("Z1 check, d1 = 1e4 with the subdivided enclosure:", [ (k, lemma_ok(arb(k), 10**4)[1].str(5)) for k in ("2.1", "2.3", "2.5") ])
