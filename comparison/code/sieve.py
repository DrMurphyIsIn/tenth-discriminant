"""CMP-2 R0 code, module 2: the auxiliary inert prime rows (lead, 2026-10-25). Derivation: the paper, Section 5
(reviewed). Inputs: band ends and rows (a, b, kappa, [n, h]), PARAMETERS ONLY; in this release they are OUR rows, from
data/own_<Q0>_<Q1>.json (fields a, b, k, sieve_n), made by own_params.py."""
import json, math
from flint import arb, fmpq, ctx
import primes as P
ctx.prec = 256
def Qform(q, a, b): return (fmpq(2 * a + b, 2)) ** 2 + fmpq(q * b * b, 4)
def split_pairs(Q0, Q1):
    lim = fmpq(Q0, 4) ** 2; out = []
    bmax = int(math.isqrt(int(4 * lim / Q1)) + 2)
    for b in range(1, bmax + 1):
        for a in range(-b, int(math.isqrt(int(lim))) + 2):
            if 2 * a + b > 0 and math.gcd(a, b) == 1 and Qform(Q1, a, b) < lim: out.append((Qform(Q1, a, b), a, b))
    out.sort(); return [(a, b) for _, a, b in out]
def row_check(Q0, Q1, row):
    a2, b2, kap = row['a'], row['b'], arb(fmpq(*map(int, row['k'].split('/'))) if '/' in row['k'] else fmpq(int(row['k'])))
    n, h = row['sieve_n']
    pairs = split_pairs(Q0, Q1)[:n]
    pp = [Qform(Q1, a, b) for a, b in pairs]; pm = [Qform(Q0, a, b) for a, b in pairs]
    rs = [r for r in P._P if 7 < r and fmpq(r) < fmpq(Q0, 4)][:h]
    assert len(rs) == h and len(pairs) == n
    U0, U1 = arb(2) ** a2, arb(2) ** b2
    assert U0 > Q1 and all(U0 > arb(x) for x in pp), "need U > Q1 and U > p_j^+"
    vm, vp = arb(Q0).sqrt() / 2, arb(Q1).sqrt() / 2
    u = 2 * sum((arb(1) / arb(x) for x in pp), arb(0)) + sum((arb(1) / r ** 2 for r in rs), arb(0))
    u2 = 2 * sum((arb(1) / arb(x) ** 2 for x in pp), arb(0)) + sum((arb(1) / r ** 4 for r in rs), arb(0))
    um = 2 * sum((arb(1) / arb(x) for x in pm), arb(0)) + sum((arb(1) / r ** 2 for r in rs), arb(0))
    assert um < 1, "u at the minus endpoints must be < 1"
    z = 2 * sum((1 / arb(x).sqrt() for x in pm), arb(0)) + sum((arb(1) / r for r in rs), arb(0))
    z2 = 2 * sum((arb(1) / arb(x) for x in pm), arb(0)) + sum((arb(1) / r ** 2 for r in rs), arb(0))
    m0 = 2 * n + h
    A = arb.pi() / (4 * vm) * arb(fmpq(768, 1225)) * (1 - u + (u * u - u2) / 2)
    B = arb.pi() / 4 * (1 + 1 / vm ** 2).sqrt() * arb(fmpq(96, 35)) * (1 + z + (z * z - z2) / 2)
    C = 2 * arb.pi() * (vp + 1 / vp) * (1 + fmpq(m0 * (m0 + 1), 2))
    m = U0.log(); d, c = P.d_low(m), P.c_up(m)
    def G(x): return kap * d - c - (x + kap.log()) * (A * (kap - 1) + B * (1 + kap.sqrt()) * (-x / 2).exp() + C * (-x).exp())
    x0, x1 = U0.log(), U1.log()
    assert x0 + kap.log() > 4
    g0, g1 = G(x0), G(x1)
    return (g0 > 0 and g1 > 0), g0, g1
