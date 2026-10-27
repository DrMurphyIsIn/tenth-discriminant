"""CMP-2 R0 code, module 1: certified prime-sum bounds (lead, 2026-10-25; Arb via python-flint, outward rounding).
Derivation: the paper, Section 5 (RS 1962 read at source: Table I, with page cites, in the frozen
data/rs_table_I.json, md5 2fc5051e asserted). No v6.1 file is read here."""
import hashlib, json, math
from flint import arb, fmpq, ctx
ctx.prec = 256
import os
TABLE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data', 'rs_table_I.json')
_raw = open(TABLE, 'rb').read()
assert hashlib.md5(_raw).hexdigest() == '2fc5051eabfbb43df7fea0b63dfd7101'
_rows = [(fmpq(*map(int, (r['b'] + '/1').split('/')[:2])) if '.' not in r['b'] else fmpq(int(r['b'].replace('.', '')), 10 ** len(r['b'].split('.')[1])),
          fmpq(int(r['mant'].replace('.', '')), 10 ** (len(r['mant'].split('.')[1]) + r['n']))) for r in json.loads(_raw)['rows']]
_rows.sort(key=lambda t: t[0])
E_RS = arb('-1.332582275733221') + arb(0, fmpq(1, 10 ** 15))   # RS 1962 (2.11), p. 65: -1.33258 22757 33221 (15 decimals). v1.4.0 FIX: v1.3.0 used the p. 76
# 'approximation' -1.33258 22757 33220 87 with a +/-1e-17 ball, which EXCLUDES the true E = -1.33258227573322088176... by 1.77e-18
# (computed independently by bb and the lead). The effect on every gap is about 1e-17, far below the gaps and the Arb radii.
C0 = arb(fmpq(101624, 100000))                                   # RS Thm 9 (3.32): theta(x) < 1.01624 x for x > 0
def eps_table(m):
    """Table I: (1 - eps) x < psi(x) < (1 + eps) x for x >= e^b; returns eps for the largest b <= m, or None."""
    best = None
    for b, e in _rows:
        if arb(b) <= m: best = e
    return best
def c_up(m):
    """theta(x)/x < c_up(m) for all x with log x >= m (m > 0)."""
    m = arb(m); cands = [C0, 1 + 1 / (2 * m)]                     # Thm 9; Thm 4 (3.15) (x > 1; decreasing in log x)
    e = eps_table(m)
    if e is not None: cands.append(1 + arb(e))                   # Table I + theta <= psi
    return min(cands, key=lambda z: z.upper())
def d_low(m):
    """theta(x)/x > d_low(m) for all x with log x >= m; 0 if no form applies (bb L4)."""
    m = arb(m); cands = [arb(0)]
    if m >= arb(563).log(): cands.append(1 - 1 / (2 * m))           # Thm 4 (3.14), x >= 563
    e = eps_table(m)
    if e is not None: cands.append(1 - arb(e) - arb(fmpq(102, 100)) * (-m / 2).exp() - 3 * (-2 * m / 3).exp())   # Table I + Cor (3.39)
    return max(cands, key=lambda z: z.lower())
def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b"\0\0"
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]: s[p * p::p] = bytearray(len(s[p * p::p]))
    return [i for i in range(n + 1) if s[i]]
_P = primes_upto(10 ** 6)
def theta_exact(x):
    return sum((arb(p).log() for p in _P if p <= x), arb(0))
def A_low(x):
    """A(x) = sum_{p<=x} log p/p > log x + E - 1/(2 log x), x > 1 (RS (3.21))."""
    L = arb(x).log(); return L + E_RS - 1 / (2 * L)
def B_H(H, P=10 ** 4):
    """certified upper bound for sum_{p>H} log p/p^2: exact to P, then partial summation with Thm 9 (2 c0/P - theta(P)/P^2)."""
    head = sum((arb(p).log() / p ** 2 for p in _P if H < p <= P), arb(0))
    return head + 2 * C0 / P - theta_exact(P) / arb(P) ** 2
def small_prime_consts(H, t):
    t = arb(t); ps = [p for p in _P if p <= H]
    aH = sum((arb(p).log() / p for p in ps), arb(0))
    thH = sum((arb(p).log() for p in ps), arb(0))
    WH = sum((arb(p).log() * (t - p * t * t / 3) for p in ps), arb(0))
    return aH, thH, WH
if __name__ == "__main__":
    # self-checks against direct computation where possible (no comparison with v6.1 here)
    for m in (6.5, 12.5, 18.4, 20, 25, 31):
        x = int(math.exp(m)) + 1
        if x <= 10 ** 6:
            th = theta_exact(x) / x
            print(f"m = {m}: d_low = {d_low(m).str(8)}, theta(e^m)/e^m = {th.str(8)}, c_up = {c_up(m).str(8)}; sandwich ok: {d_low(m) < th < c_up(m)}")
        else:
            print(f"m = {m}: d_low = {d_low(m).str(10)}, c_up = {c_up(m).str(10)}")
    for x in (2, 10, 100, 319, 10 ** 4, 10 ** 6):
        A = sum((arb(p).log() / p for p in _P if p <= x), arb(0))
        print(f"A({x}) = {A.str(10)} > A_low = {A_low(x).str(10)}: {A > A_low(x)}")
    aH, thH, WH = small_prime_consts(21, fmpq(3, 64))
    print("H = 21, t = 3/64: a_H", aH.str(10), "theta_H", thH.str(10), "W_H", WH.str(10), "; B_21 <=", B_H(21).str(10))
