"""CMP-3 C1a under the MODERN profile (modern_profile v2) with the [548,550] band data (rows, gamma, kernel). Adapted from cmp2/r0code/c1a.py.
C1a (truth sandwich) at q = 163, 67, 43 (lead, 2026-10-25; bb entry 8 refinements a-e). Each field has h = 1, so every inequality
is a THEOREM there wherever its hypotheses hold. NAMED FAILED HYPOTHESIS: the auxiliary-prime SIEVE (R0 part 1 section 3, G > 0)
certifies no row at these q (v = sqrt(q)/2 small; few split pairs below (q/4)^2), so C1b (the certificate must not pass) is
IMPOSSIBLE by this route. C1a runs on the rest, with the auxiliary inert primes' existence VERIFIED DIRECTLY from the actual
primes for U <= 1e8 (rows with 2^b * kappa <= 1e8) and ASSUMED above that (true by density; not proved here).
Checks: (i) L_stage(x) <= T_q(e^x) for every stage, x in [12, log 1e8]; (ii) lower <= sum_{p<=1e8} (log p/p) W(log p) (no tail
needed: the tail is >= 0); (iii) sum_noninert (log p/p) W(log p) <= U(q), with a rigorous tail via W(y) <= int_y^oo h (f <= 1) and RS
increments; (iv) the section-7 identity int h(x) T_{<=P}(e^x) dx = sum_{p<=P} (log p/p) W(log p) at P = 1e6."""
import copy, math, sys
import numpy as np
import mpmath as mp
from flint import arb, fmpq, ctx
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'code'))
import json
import primes as PRM, assemble as AS, outer as O, modern_profile as MP
PRM.c_up = MP.c_up; PRM.d_low = MP.d_low; PRM.C0 = MP.C_UP; AS.A_CORR = MP.A_corr
BANDFILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data', 'modern_548_550.json')
ctx.prec = 512
PMAX = 10 ** 8
s = np.ones(PMAX + 1, dtype=bool); s[:2] = False
for p in range(2, int(PMAX ** 0.5) + 1):
    if s[p]: s[p * p::p] = False
PR = np.nonzero(s)[0]
def noninert_and_inert(Q):
    odd = PR[(PR != 2) & (PR != Q)]; e = (Q - 1) // 2; res = np.ones(len(odd), dtype=np.int64); b = (odd % Q).astype(np.int64)
    while e:
        if e & 1: res = (res * b) % Q
        b = (b * b) % Q; e >>= 1
    non = np.sort(np.concatenate([odd[res == 1], np.array([Q])])); ine = np.sort(np.concatenate([odd[res != 1], np.array([2])]))
    return non, ine
for Q in [int(a) for a in sys.argv[1:]] or [163, 67, 43]:
    non, ine = noninert_and_inert(Q)
    assert non[0] > Q / 4 and Q % 8 == 3, "h = 1 sanity"
    lw = np.log(non.astype(np.float64)) / non
    def T(X):
        m = non <= X; u = non[m] / X; a = np.floor(1 / u); return float(np.sum(lw[m] * (2 * a * u - a * (a + 1) * u * u)))
    J = json.load(open(BANDFILE)); band = copy.deepcopy(J['band']); band['q0'] = band['q1'] = Q; AS.gam = arb(fmpq(*map(int, band['gamma'].split('/'))))
    ok_aux = []
    for r in band['rows']:
        _n, _d = map(int, r['k'].split('/')); kap = _n / _d; lo, hi = 2.0 ** r['a'], kap * 2.0 ** r['b']
        if hi <= PMAX:
            seg = ine[(ine > lo) & (ine <= hi)]; ok_aux.append(len(seg) > 1 and np.max(seg[1:] / seg[:-1]) < kap and seg[0] <= kap * lo)
    print(f"q = {Q}: first noninert prime {non[0]} (> q/4 = {Q/4}); aux inert primes VERIFIED for {sum(ok_aux)}/{len(ok_aux)} rows with kappa 2^b <= 1e8; rest ASSUMED")
    worst_all = []
    for st in range(0, band['stages'] + 1):
        segs = AS.build(band, OURS_A=True, stages=st)
        worst = None
        for k in range(0, 400):
            x = 12.0 + 0.02 * k
            if x > math.log(PMAX): break
            Lx = float(AS.envelope_eval(segs, arb(x)).mid().str(20, radius=False)); Tx = T(math.exp(x))
            if worst is None or Tx - Lx < worst[1]: worst = (x, Tx - Lx, Lx, Tx)
        first_pos = next((12.0 + 0.02 * k for k in range(400) if float(AS.envelope_eval(segs, arb(12.0 + 0.02 * k)).mid().str(10, radius=False)) > 0), None)
        worst_all.append(worst[1])
        print(f"   (i) stage {st}: min (T - L) = {worst[1]:+.5f} at x = {worst[0]:.2f} (L {worst[2]:.4f}, T {worst[3]:.4f}); L first positive at x = {first_pos}")
    c, dj = O.kernel(band); Fd = [O.Fw(d) for d in dj]
    def W(y):
        y = arb(y); return sum((c[j] * Fd[j] * (-dj[j] * y).exp() for j in range(len(c))), arb(0))
    def Wbound(y):                                   # int_y^oo h = sum c_j e^{-d_j y}, >= W(y) since f <= 1
        y = arb(y); return sum((c[j] * (-dj[j] * y).exp() for j in range(len(c))), arb(0))
    ys = np.log(non.astype(np.float64)); step = 0.002
    edges = np.arange(math.log(2), math.log(PMAX) + step, step)
    cnt = np.histogram(ys, bins=edges, weights=lw)[0]
    Wv = [W(float(y)) for y in edges]
    part_lo = sum((Wv[i + 1] * float(cnt[i]) for i in range(len(cnt)) if cnt[i] > 0), arb(0))
    part_hi = sum((Wv[i] * float(cnt[i]) for i in range(len(cnt)) if cnt[i] > 0), arb(0))
    tail = sum((Wbound(math.log(PMAX) + k) * (1 + 1 / (2 * (math.log(PMAX) + k)) + 1 / (2 * (math.log(PMAX) + k + 1))) for k in range(400)), arb(0))
    segs = AS.build(band, OURS_A=True)
    low = O.lower_bound(segs, c, dj)
    main = arb(0); err = arb(0)
    for j in range(len(c)):
        H, EH = O.H_and_EH(Q, dj[j]); main += c[j] * Fd[j] * H; err += abs(c[j]) * Fd[j] * EH
    up = main + err + arb(Q).log() / (2 * (Q - 1))
    print(f"   (ii) lower = {low.str(10)} <= partial sum (p <= 1e8, W-monotone lower) {part_lo.str(10)}: {low < part_lo}; margin {(part_lo - low).str(6)}")
    print(f"   (iii) full sum <= {(part_hi + tail).str(10)} <= U = {up.str(10)}: {(part_hi + tail) < up}; margin {(up - part_hi - tail).str(6)}")
    print(f"   C1b gap (lower - U) = {(low - up).str(8)}; NOTE C1b is impossible by this route (sieve hypothesis fails), reported for information")
    print(f"   (iv) identity check deferred (the float kernel h cancels catastrophically; needs Arb quadrature) -- TODO")
