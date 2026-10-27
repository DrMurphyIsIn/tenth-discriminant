"""C9 truth test (KT-CMP3), reader-1 transcription vs EXACT theta(x) for x <= XMAX. NUMERICAL (float64 cumulative log-sum,
relative error about 1e-8, far below every eps tested; not a certificate). Within each prime gap [p_n, p_{n+1}):
(x - theta)/x * (log x)^k and (x - theta)/sqrt(x) increase in x, so their sup is at x -> p_{n+1}-; (x - theta)/sqrt(x) has its inf at
x = p_n. Each transcribed value is bumped up by one unit in its last digit (BKLNW p. 25)."""
import json, math, sys
import numpy as np
XMAX = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 9
import os
T = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data', 'transcription_theta_bounds.json')))
def bump(s):
    m, e = s.lower().split('e'); d = len(m.split('.')[1]) if '.' in m else 0
    return float(m) * 10 ** int(e) + 10 ** (int(e) - d)
s = np.ones(XMAX + 1, dtype=np.bool_); s[:2] = False
for p in range(2, int(XMAX ** 0.5) + 1):
    if s[p]: s[p * p::p] = False
P = np.nonzero(s)[0].astype(np.float64); del s
th = np.cumsum(np.log(P))                       # theta(p_n)
nxt = np.append(P[1:], float(XMAX))              # x -> p_{n+1}- (or XMAX)
fails = []
# Table 13 rows within range
for r in T['BKLNW_Table13']['rows']:
    a, b = float(r['a']), float(r['b'])
    if b > XMAX: continue
    sel = (nxt > a) & (P < b)                    # gaps meeting [a, b)
    x = np.minimum(nxt[sel], b); th_ = th[sel]
    for k, Ds in enumerate(r['D']):
        if a < 2: x2 = np.maximum(x, 2.0)
        else: x2 = x
        v = ((x2 - th_) / x2 * np.log(x2) ** k).max()
        ok = v <= bump(Ds); print(f"T13 [{r['a']},{r['b']}) k={k}: max={v:.6e} <= D={bump(Ds):.6e} {ok}")
        if not ok: fails.append(('T13', r['a'], k))
    # the region [a, p_first) before the first prime >= a when a is not prime: theta constant = theta(prev prime); covered by sel
# Buthe (1.6): x - theta <= 1.95 sqrt(x), 1423 <= x <= XMAX
for lo in (1423, 1427):
    sel = P >= lo                                 # gaps [p_n, p_{n+1}) with p_n >= lo lie inside [lo, XMAX]
    g = (nxt[sel] - th[sel]) / np.sqrt(nxt[sel]); i = int(np.argmax(g)); v = float(g[i])
    print(f"Buthe(1.6) from x >= {lo}: max (x-theta)/sqrt(x) = {v:.5f} at x -> {int(nxt[sel][i])}- : <= 1.95 {v <= 1.95}")
    if v > 1.95: fails.append(('B16', lo, int(nxt[sel][i])))
    # the gap containing lo itself (p_n < lo <= x < p_{n+1}):
j = np.searchsorted(P, 1423) - 1; xs = nxt[j]; print(f"  gap [{int(P[j])},{int(xs)}) meets [1423,..): (x-theta)/sqrt(x) at x->{int(xs)}- = {(xs-th[j])/math.sqrt(xs):.5f}")
# Buthe (1.7): x - theta > 0.05 sqrt(x), inf at x = p_n
v = ((P - th) / np.sqrt(P)).min(); print(f"Buthe(1.7) min (x-theta)/sqrt(x) at primes = {v:.5f} > 0.05 {v > 0.05}"); fails += [] if v > 0.05 else [('B17',)]
print(f"theta(x) < x for all x <= {XMAX:.0e}: {bool((th < P).all())}")
# Table 14 rows with X0 < XMAX: (1 - m0) x < theta(x) for X0 < x <= XMAX
for r in T['BKLNW_Table14_k0']['rows']:
    l = eval(r['logX0'].replace('log', 'math.log'))
    if l >= math.log(XMAX): continue
    X0 = math.exp(l)
    sel = nxt > X0; v = ((nxt[sel] - th[sel]) / nxt[sel]).max(); m0 = bump(r['m0'])
    print(f"T14 logX0={r['logX0']}: max (x-theta)/x on (X0, {XMAX:.0e}] = {v:.5e} < m0 = {m0:.5e} {v < m0}"); fails += [] if v < m0 else [('T14', r['logX0'])]
print("C9 FAILURES:", fails if fails else "none")
