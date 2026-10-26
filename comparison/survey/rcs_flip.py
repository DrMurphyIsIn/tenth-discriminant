"""CMP-1 'flip' (lead, 2026-10-25). (1) Read the sigma0 curve backwards: for any posted or certified D0, sigma_eq(D0) is the
zero-free abscissa that the CS route would need to reach the same D0. It puts every method on one strength scale (purely a
calibration device: it does NOT say a method proves anything about zeros). (2) Extrapolate v6.1's band margins toward q < 570."""
from flint import arb, fmpq, ctx
import json
ctx.prec = 300
import hashlib, os
_g = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rcs_grh.py')).read()
assert hashlib.md5(_g.encode()).hexdigest() == 'bfcf5805fd4d2106bd3b41612a00d2ed'   # bb D8: pinned
exec(_g.split('best = None')[0])
def sigma_for(D):
    lo, hi = arb(fmpq(1, 2)) + arb(fmpq(1, 10**6)), arb(1) - arb(fmpq(1, 10**12))
    for _ in range(120):
        mid = (lo + hi) / 2
        if dM(mid) < D: lo = mid
        else: hi = mid
    return lo
rows = [("GRH (conditional)", 199.12), ("Weber/historical q < 196 [Heegner-type, excluded]", 196), ("v6.1 light determinant (twinheterodox)", 570),
        ("7/8 half-plane", 653.99), ("11/12 half-plane", 1151.66), ("v5 light determinant", 2000), ("Bryce/Kerr + LZZ + CS", 11000),
        ("elementary determinant 2^15", 32768), ("Larsson Banks+LZZ", 50000), ("Kimi repaired (Pratt)", 160000),
        ("Kimura chain_58", 6.4668e7), ("Kimura chain_59", 1.2321e8), ("Rudolph Prop 9", 1.8935e8), ("Kimura Thm1 first part", 5.5e9),
        ("van Dijk v2", 8e9), ("Banks", 1e10), ("Kimura Thm1 second part", 1.6069e15)]
print("(1) equivalent zero-free abscissa sigma_eq(D0): the CS route reaches D0 IF no real zero in (sigma_eq, 1) for every conductor >= D0")
print("   (BMOR Prop 1.10 removed: classification-based via Watkins 2004, bb D3, like Weber)")
for name, D in sorted(rows, key=lambda r: r[1]):
    if D <= 199.13:
        print(f"   {name:52s} D0 = {D:>12.6g}   below the family floor 199.12"); continue
    s = sigma_for(arb(D))
    print(f"   {name:52s} D0 = {D:>12.6g}   sigma_eq = {s.mid().str(7)}   1 - sigma_eq = {(1 - s).mid().str(4)}")
import sys
# Part (2) is optional and reads v6.1's certificate files, which this release does NOT ship: pass the path of
# twinheterodox/versions/v6.1 (commit 44c7d6fc) as the only argument.
if len(sys.argv) < 2:
    print("\n(2) skipped: pass the path of twinheterodox's versions/v6.1 directory (commit 44c7d6fc) to run it")
else:
    print("\n(2) v6.1 band certificates (exact rationals from certificate_*.json; relative gap = (lower - upper)/upper)")
    base = os.path.join(sys.argv[1], '')
    pts = []
    for f in ['certificate_570_580.json', 'certificate_580_600.json', 'certificate_600_700.json', 'certificate_700_1050.json', 'certificate_1050_2000.json']:
        d = json.load(open(base + f))
        lo, up = fmpq(*map(int, d['lower'].split('/'))), fmpq(*map(int, d['upper'].split('/')))
        rel = (lo - up) / up
        rel = int(rel.p) / int(rel.q)
        pts.append((d["q0"], d["q1"], rel))
        print(f"   band [{d['q0']}, {d['q1']}]: relative gap {rel:.5f}")
    (a0, _, r0), (a1, _, r1) = pts[0], pts[1]
    import math
    for label, x0, x1 in [("linear in q", a0, a1), ("linear in log q", math.log(a0), math.log(a1))]:
        slope = (r1 - r0) / (x1 - x0); z = x0 - r0 / slope
        print(f"   HEURISTIC (unknown bias; bb D7) extrapolation of the first two bands, {label}: relative gap -> 0 at q ~ {z if label == 'linear in q' else math.exp(z):.1f}")
