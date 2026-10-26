"""Optional: reproduce twinheterodox v0.6.1's band [570, 580] from ITS parameters (paper, Section 5, "The reproduction").
v0.6.1's repository has no licence, so none of its files ship here: pass the path of its versions/v6.1 directory (commit
44c7d6fc) as the only argument. Only parameters.json is read (the band ends, rows and kernel), and its method constants are
checked against the ones written into assemble.py. Faithful configuration: v0.6.1's Mertens constant 1.334 (OURS_A=False) and
v0.6.1's closed form (29) for K(j) (USE_KCERT=False); v0.6.1's own lower bound is 10.975413160309."""
import hashlib, json, os, sys
from flint import arb, fmpq
if len(sys.argv) < 2: sys.exit("usage: python3 repro_v61.py <path to twinheterodox versions/v6.1>")
import assemble as AS, outer as O
raw = open(os.path.join(sys.argv[1], 'parameters.json'), 'rb').read()
assert hashlib.md5(raw).hexdigest() == '856b3875b008636fcc325b7481007e3c', 'not v0.6.1 at commit 44c7d6fc'
par = json.loads(raw)
for k, ours in (('t', fmpq(3, 64)), ('C', fmpq(27, 64)), ('tau', fmpq(3, 10)), ('gamma', fmpq(3, 10))):
    assert AS.fq(par[k]) == ours, (k, par[k])                    # the constants written into assemble.py
band = par['bands'][0]; Q0 = band['q0']
assert (Q0, band['q1']) == (570, 580)
AS.USE_KCERT = False
segs = AS.build(band, OURS_A=False)
c, dj = O.kernel(band)
print(f"v0.6.1 parameters, faithful configuration: lower bound on [{Q0}, {band['q1']}] = {O.lower_bound(segs, c, dj).str(15)}")
print("v0.6.1's own value: 10.975413160309")
