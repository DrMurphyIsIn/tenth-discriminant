"""CMP-2: OUR OWN parameters for a band (the theorem must not depend on v6.1's optimised data; v6.1's repository has no licence, and nothing of it is copied).
Rows: a = 18..53, b = a + 1; for each row choose (n, h) from a small grid and the MINIMAL kappa (bisection on the certified G test);
rows that cannot be certified are dropped. gamma = max beta/4 rounded up. Kernel: integer P from the eigenproblem on OUR envelope,
over a few (degree, d, e). Only the STRUCTURE (rows indexed by a, b = a + 1; kernel family e^{-dx} P(e^{-ex})^2) follows v6.1; no
numbers are taken from its files."""
import copy, json, math, sys
from flint import arb, fmpq
import assemble as AS, sieve as SV, outer as O, x2_kernel as X2, band81 as B
def own_rows(Q0, Q1):
    avail = len(SV.split_pairs(Q0, Q1)); hav = len([q for q in SV.P._P if 7 < q and fmpq(q) < fmpq(Q0, 4)])
    ngrid = sorted(set([0, 4, 16, 64, 256, avail])); hgrid = sorted(set([0, 4, hav]))
    rows, dropped = [], []
    for a in range(18, 54):
        best = None
        for n in ngrid:
            if n > avail: continue
            for h in hgrid:
                r = {'a': a, 'b': a + 1, 'k': '3/1', 'sieve_n': [n, h]}
                def ok(k):
                    r['k'] = f"{k.p}/{k.q}"
                    try: return SV.row_check(Q0, Q1, r)[0]
                    except AssertionError: return False
                if not ok(fmpq(3)): continue
                lo, hi = fmpq(1001, 1000), fmpq(3)
                for _ in range(22):
                    mid = (lo + hi) / 2
                    if ok(mid): hi = mid
                    else: lo = mid
                k = fmpq(int((hi * 10 ** 6).floor()) + 1, 10 ** 6)
                if ok(k) and (best is None or k < best[0]): best = (k, n, h)
        if best is None: dropped.append(a); continue
        rows.append({'a': a, 'b': a + 1, 'k': f"{best[0].p}/{best[0].q}", 'sieve_n': [best[1], best[2]]})
    return rows, dropped
def own_band(Q0, Q1, specs):
    rows, dropped = own_rows(Q0, Q1)
    band = {'q0': Q0, 'q1': Q1, 'rows': rows, 'stages': 8}
    betas = [AS.row_constants(Q0, Q1, r['a'])['beta'] for r in rows]
    gf = float(arb(max(b.upper() for b in betas) / 4).upper().str(25, radius=False)); gnew = fmpq(math.ceil(gf * 10 ** 4) + 1, 10 ** 4)
    AS.gam = arb(gnew); band['gamma'] = f"{gnew.p}/{gnew.q}"
    segs = AS.build(band, OURS_A=True)
    best = None
    for (n, d, e) in specs:
        P, ev = X2.best_P(band, n, d, e, segs)
        gap, err = X2.gap_for(band, P, f"{d[0]}/{d[1]}", f"{e[0]}/{e[1]}", segs)
        if best is None or gap > best[0]: best = (gap, err, n, d, e, P)
    gap, err, n, d, e, P = best
    band['kernel'] = {'delta': f"{d[0]}/{d[1]}", 'epsilon': f"{e[0]}/{e[1]}", 'polynomial': [str(p) for p in P]}
    c, dj = O.kernel(band)
    Up, rem, ok81 = B.check_band(c, dj, Q0, Q1, AS.gam)
    mono = all(B.Hparts(Q0, dj[j])[3] * B.Hparts(Q0, dj[j])[2] > 1 + B.Hparts(Q0, dj[j])[0] / B.Hparts(Q0, dj[j])[1] for j in range(len(c)))
    res = dict(Q0=Q0, Q1=Q1, rows=len(rows), dropped=dropped, gamma=band['gamma'], degree=n, d=band['kernel']['delta'], e=band['kernel']['epsilon'],
               gap_at_Q0=gap.str(10), x1_err=err.str(3), Uprime=Up.str(6), ok81=bool(ok81), H_mono=bool(mono), CERTIFIED_BAND=bool(gap > 0 and ok81 and mono))
    json.dump({'result': res, 'band': band}, open(f"own_{Q0}_{Q1}.json", 'w'), indent=1)
    return res
if __name__ == "__main__":
    Q0, Q1 = int(sys.argv[1]), int(sys.argv[2])
    specs = [(16, (3, 10), (1, 25)), (18, (3, 10), (1, 25)), (20, (1, 4), (1, 25)), (20, (3, 10), (1, 25)), (16, (2, 5), (1, 20))]
    print(json.dumps(own_band(Q0, Q1, specs)), flush=True)
