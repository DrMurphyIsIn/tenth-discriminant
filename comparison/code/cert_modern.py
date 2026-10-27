"""v1.4.0: certify the five bands [548, 565] under the modern explicit bounds for theta (paper §sec:modern; modern_profile.py), from the
frozen band data data/modern_<Q0>_<Q1>.json (rows, kappa, sieve sizes, gamma, kernel). The same three obligations as own_cert_all.py:
(1) the gap at Q0 > 0 (X1-abs, integer kernel); (2) section 8.1 on 8 Taylor cells; (3) the exact H-monotonicity criterion. The rows'
sieve tests are re-checked under the profile. Prime slots replaced: c_up, d_low, C0 and the (3.21) correction (assemble.A_CORR)."""
import json, os, sys
from flint import arb, fmpq
import primes as PR, assemble as AS, x2_kernel as X2, band81 as B, outer as O, sieve as SV, modern_profile as MP
PR.c_up = MP.c_up; PR.d_low = MP.d_low; PR.C0 = MP.C_UP; AS.A_CORR = MP.A_corr
DATA = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data')
out = []
for Q0, Q1 in [(548, 550), (550, 553), (553, 556), (556, 560), (560, 565)]:
    band = json.load(open(os.path.join(DATA, f"modern_{Q0}_{Q1}.json")))['band']
    rows_ok = all(SV.row_check(Q0, Q1, r)[0] for r in band['rows'])
    AS.gam = arb(fmpq(*map(int, band['gamma'].split('/'))))
    betas = [AS.row_constants(Q0, Q1, r['a'])['beta'] / 4 for r in band['rows']]
    beta_ok = all(b4 < AS.gam for b4 in betas); maxb4 = max(betas, key=lambda z: z.upper())
    segs = AS.build(band, OURS_A=True)
    k = band['kernel']; P = [int(p) for p in k['polynomial']]
    gap, err = X2.gap_for(band, P, k['delta'], k['epsilon'], segs)
    c, dj = O.kernel(band)
    worst, ok81 = B.check_band_cells(c, dj, Q0, Q1, AS.gam, ncells=8)
    mono = all(B.Hparts(Q0, dj[j])[3] * B.Hparts(Q0, dj[j])[2] > 1 + B.Hparts(Q0, dj[j])[0] / B.Hparts(Q0, dj[j])[1] for j in range(len(c)))
    r = dict(Q0=Q0, Q1=Q1, rows=len(band['rows']), rows_sieve_ok=bool(rows_ok), beta_ok=bool(beta_ok), max_beta_over_4=maxb4.str(8), gamma=band['gamma'], degree=len(P) - 1, d=k['delta'], e=k['epsilon'],
             gap_at_Q0=gap.str(12), x1_err=err.str(4), Uprime_worst=worst.str(6), ok81=bool(ok81), H_mono=bool(mono),
             CERTIFIED_BAND=bool(rows_ok and beta_ok and gap > 0 and ok81 and mono))
    out.append(r); print(json.dumps(r), flush=True)
print("ALL FIVE MODERN BANDS CERTIFIED:", all(r['CERTIFIED_BAND'] for r in out))
