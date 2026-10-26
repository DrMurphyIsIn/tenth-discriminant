"""CMP-1: the sigma0 family as one curve (lead, 2026-10-25; per bb REVIEW_CMP1_GRH H1). One reduction (rcs_edge.py's M and B)
on a real-zero-free segment (sigma0, 1) gives D0(sigma0) = d_M(sigma0). Rows A (7/8), B (11/12) and GRH (sigma0 -> 1/2+) are
three points of it. Inverse use: for a target D, sigma_D = the sigma0 with d_M(sigma0) = D, i.e. how far down a zero-free real
segment would have to reach, for every conductor >= D, to give d < D by this route.
Corollary (zero location): if h(-d) = 1 and d > d_M(sigma) with M(sigma, d) - B(sigma, d) > 0, then zeta_K(sigma) > 0, so
L(sigma, chi) < 0 < L(1, chi), and L(s, chi_{-d}) has a real zero in (sigma, 1). So a hypothetical tenth discriminant
d in (199.12, 653.99) would carry a real zero beta > sigma_d."""
from flint import arb, fmpq, ctx
ctx.prec = 300
import hashlib, os
_g = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'rcs_grh.py')).read()
assert hashlib.md5(_g.encode()).hexdigest() == 'bfcf5805fd4d2106bd3b41612a00d2ed'   # bb D8: pinned
exec(_g.split('best = None')[0])
def sigma_for(D):
    lo, hi = arb(fmpq(1, 2)) + arb(fmpq(1, 10**6)), arb(fmpq(99, 100))
    for _ in range(80):
        mid = (lo + hi) / 2
        if dM(mid) < D: lo = mid
        else: hi = mid
    return lo, hi
print("target D  sigma_D (d_M(sigma_D) = D)       check M - B > 0 at (sigma below sigma_D, d = D)")
for D in (1152, 654, 600, 570, 500, 400, 300, 250, 200):
    lo, hi = sigma_for(D)
    s = lo - arb(fmpq(1, 10**8))
    ok = (M(s, D) - B(s, D)) > 0
    print(f"{D:8d}  {lo.mid().str(12)}            {ok}")
