"""CMP-3 C3 (degradation, KT-CMP2 item 3 as amended): with the [548,550] band data FIXED (rows, gamma, kernel), make one prime input
1% worse and recompute the certified gap at Q0. It must DROP. Inputs: (a) eps_low x 1.01; (b) the Mertens correction A_corr x 1.01;
(c) c_up - 1 x 1.01; (d) one row's kappa x 1.01 (row a = 30). Baseline = the frozen gap."""
import json, sys, copy
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'code'))
from flint import arb, fmpq
import primes as PRM, assemble as AS, x2_kernel as X2, modern_profile as MP
mode = sys.argv[1]
J = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data', 'modern_548_550.json'))); band = copy.deepcopy(J['band'])
k = fmpq(101, 100)
PRM.c_up = MP.c_up; PRM.d_low = MP.d_low; PRM.C0 = MP.C_UP; AS.A_CORR = MP.A_corr
if mode == 'eps': PRM.d_low = lambda m: 1 - MP.eps_low(m) * k
if mode == 'mertens': AS.A_CORR = lambda L: MP.A_corr(L) * k
if mode == 'cup': PRM.c_up = lambda m: 1 + (MP.C_UP - 1) * k; PRM.C0 = 1 + (MP.C_UP - 1) * k
if mode == 'kappa':
    for r in band['rows']:
        if r['a'] == 30: r['k'] = str(AS.fq(r['k']) * k).replace(' ', '')
AS.gam = arb(fmpq(*map(int, band['gamma'].split('/'))))
segs = AS.build(band, OURS_A=True)
P = [int(p) for p in band['kernel']['polynomial']]
gap, err = X2.gap_for(band, P, band['kernel']['delta'], band['kernel']['epsilon'], segs)
print(json.dumps(dict(mode=mode, gap_at_Q0=gap.mid().str(12, radius=False))), flush=True)
