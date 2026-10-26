"""CMP-2 X2 (lead): the eigenproblem in best_P is only a SEARCH; the claim is gap_for's Arb certificate. The optimal kernel e^{-dx} P(e^{-ex})^2 on OUR envelope L for band
[Q0, Q0+10]; P from the top generalized eigenvector (mpmath, 250 digits), rounded to INTEGERS (h stays >= 0 exactly), then the gap
is certified in Arb with X1-abs errors. The rows are fixed here (own_params.py chooses them)."""
import copy, sys
import mpmath as mp
from flint import arb, fmpq
import outer as O, assemble as AS
mp.mp.dps = 250
def a2m(x): return mp.mpf(x.mid().str(240, radius=False))
def gap_for(band, P, d0, e0, segs):
    band = copy.deepcopy(band); band['kernel'] = {'delta': str(d0), 'epsilon': str(e0), 'polynomial': [str(int(c)) for c in P]}
    c, dj = O.kernel(band)
    low = O.lower_bound(segs, c, dj)
    main = arb(0); err = arb(0)
    for j in range(len(c)):
        H, EH = O.H_and_EH(band['q0'], dj[j], q1=band['q1']); main += c[j] * O.Fw(dj[j]) * H; err += abs(c[j]) * O.Fw(dj[j]) * EH
    ram = arb(band['q0']).log() / (2 * (band['q0'] - 1))
    return low - main - err - ram, err
def best_P(band, n, d0, e0, segs):
    djs = [arb(fmpq(*d0)) + j * arb(fmpq(*e0)) for j in range(2 * n + 1)]
    cells, xlast = O.selection_cells(O.exactify(segs))
    ex = O.exactify(segs)
    def lapL(dd):
        acc = arb(0)
        for a, b, i in cells:
            if i is None: continue
            x0, x1, A, D = ex[i]; lo, hi = arb(a), arb(b)
            if hi <= x0: continue
            if lo < x0: lo = x0
            if hi <= x1: acc += O.lap_affine(dd, lo, hi, A, D)
            elif lo >= x1: acc += O.lap_affine(dd, lo, hi, arb(0), -(A * x1 - D))
            else: acc += O.lap_affine(dd, lo, x1, A, D) + O.lap_affine(dd, x1, hi, arb(0), -(A * x1 - D))
        frozen = max((A * x1 - D for x0, x1, A, D in ex), key=lambda z: z.lower())
        return acc + O.lap_affine(dd, arb(xlast), None, arb(0), -frozen)
    g = []
    for dd in djs:
        H, EH = O.H_and_EH(band['q0'], dd)
        g.append(a2m(lapL(dd) - O.Fw(dd) * H / dd))
    G = mp.matrix(n + 1, n + 1); Hm = mp.matrix(n + 1, n + 1)
    for i in range(n + 1):
        for j in range(n + 1):
            G[i, j] = g[i + j]; Hm[i, j] = 1 / a2m(djs[i + j])
    Lc = mp.cholesky(Hm); Li = mp.inverse(Lc); S = Li * G * Li.T; S = (S + S.T) / 2
    ev, V = mp.eigsy(S); k = max(range(n + 1), key=lambda i: ev[i])
    p = Li.T * V[:, k]
    sc = mp.mpf(10) ** 40 / max(abs(p[i]) for i in range(n + 1))
    return [int(mp.nint(p[i] * sc)) for i in range(n + 1)], ev[k]
