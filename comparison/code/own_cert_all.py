"""Final certification of the four OWN-parameter bands (rows, kappa, sieve sizes, gamma, kernels all ours; t, C, tau and the
8 stages are v6.1's method constants): (1) gap at Q0 > 0 (X1-abs, band-uniform log factor); (2) section 8.1 on 8 Taylor cells;
(3) exact H-monotonicity criterion. Reads own_<Q0>_<Q1>.json from ../data, or from the directory given as the only argument."""
import json, os, sys
from flint import arb, fmpq
import assemble as AS, outer as O, band81 as B, x2_kernel as X2
DATA = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data')
out = []
for Q0, Q1 in [(565, 570), (570, 580), (580, 600), (600, 652)]:
    band = json.load(open(os.path.join(DATA, f"own_{Q0}_{Q1}.json")))['band']
    AS.gam = arb(fmpq(*map(int, band['gamma'].split('/'))))
    segs = AS.build(band, OURS_A=True)
    k = band['kernel']; P = [int(p) for p in k['polynomial']]
    gap, err = X2.gap_for(band, P, k['delta'], k['epsilon'], segs)
    c, dj = O.kernel(band)
    worst, ok81 = B.check_band_cells(c, dj, Q0, Q1, AS.gam, ncells=8)
    mono = all(B.Hparts(Q0, dj[j])[3] * B.Hparts(Q0, dj[j])[2] > 1 + B.Hparts(Q0, dj[j])[0] / B.Hparts(Q0, dj[j])[1] for j in range(len(c)))
    r = dict(Q0=Q0, Q1=Q1, rows=len(band['rows']), gamma=band['gamma'], degree=len(P) - 1, d=k['delta'], e=k['epsilon'],
             gap_at_Q0=gap.str(12), x1_err=err.str(4), Uprime_worst=worst.str(6), ok81=bool(ok81), H_mono=bool(mono),
             CERTIFIED_BAND=bool(gap > 0 and ok81 and mono))
    out.append(r); print(json.dumps(r), flush=True)
print("ALL FOUR BANDS CERTIFIED:", all(r['CERTIFIED_BAND'] for r in out))
