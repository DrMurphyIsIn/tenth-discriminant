"""CMP-2 R0 code, module 4: the outer comparison at q = Q0 (lead, 2026-10-25). lower = int h L_sel (L_sel a piecewise selection
from OUR envelope, a valid lower bound since h >= 0); upper = sum c_i F(d_i) H_q(d_i) + sum |c_i| F(d_i) E_H(d_i) + log Q0/(2(Q0-1)).
Derivations: the paper, Sections 5 and 6; the error formula (41) and the ramified allowance re-derived by us.
Error accounting: X1-abs (the exact Poisson modes, paper Section 6). Inputs: kernel (d, e, P) = PARAMETERS."""
import json
from flint import arb, arb_series, fmpq, ctx
import assemble as AS, sieve as SV
ctx.prec = 512
def fq(s): return fmpq(*map(int, s.split('/'))) if '/' in s else fmpq(*([int(s.replace('.', '')), 10 ** len(s.split('.')[1])] if '.' in s else [int(s), 1]))
def zeta_d(s):                       # zeta(s), zeta'(s) rigorously
    z = arb_series([s, 1], prec=2).zeta(); return z[0], z[1]
def mode_bounds(s, v, N0=6, vplus=None):
    """X1-abs: E_A >= sum |modes|, E_N >= sum |d/ds modes| at this v (sharp even-cosh K bounds; tail by geometric series)."""
    EA = arb(0); EN = arb(0); nu = s - arb(1) / 2
    for b in range(1, 40):
        for n in range(1, 40):
            x = 2 * arb.pi() * n * b * v
            Kb = (arb.pi() / (2 * x)).sqrt() * (-x + nu * nu / (2 * x)).exp()
            dKb = nu / x * Kb
            pref = 4 * arb.pi() ** s * arb(n) ** (s - arb(1) / 2) * (b * v) ** (arb(1) / 2 - s) / s.gamma()
            term = pref * Kb
            # bb M4 / X1b: the log factor can GROW with v, so take its max over the band ends v- (= v) and v+; mode bound stays at v-
            lf = abs(arb.pi().log() + arb(n).log() - (b * v).log() - s.digamma())
            if vplus is not None:
                lf = max(lf, abs(arb.pi().log() + arb(n).log() - (b * vplus).log() - s.digamma()), key=lambda z: z.upper())
            EA += term; EN += term * lf + pref * dKb
    # tail n*b >= 40: each term <= 4 pi^s m^s v^(1/2-s) ... * e^(-2 pi v m) with d(m) <= m: crude geometric bound
    x = 2 * arb.pi() * 40 * v
    tail = 4 * arb.pi() ** s * 1600 * arb(40) ** (s + 1) * (arb.pi() / (2 * x)).sqrt() * (-x + nu * nu / (2 * x)).exp() / s.gamma() * 10
    return EA + tail, EN + tail * 100
def H_and_EH(q, d, q1=None):
    s = 1 + d; v = arb(q).sqrt() / 2
    C = arb.pi().sqrt() * (s - arb(1) / 2).gamma() / s.gamma()
    z21, dz21 = zeta_d(2 * s - 1); z2, dz2 = zeta_d(2 * s)
    Fq = C * v ** (1 - 2 * s) * z21
    cs = -2 * dz2 / z2
    g = s.digamma() - (s - arb(1) / 2).digamma()
    kap = g - 2 * dz21 / z21 - cs
    H = Fq * ((arb(q) / 4).log() + kap) / (2 * (z2 + Fq))
    EA, EN = mode_bounds(s, v, vplus=(arb(q1).sqrt() / 2 if q1 is not None else None))
    EH = (EN + (cs + 2 * H) * EA) / (2 * (1 - EA))
    return H, EH
def Fw(d): return 2 * d * (1 + d).zeta() / ((1 + d) * (2 + d))
def kernel(band):
    k = band['kernel']; d0, e0 = arb(fq(k['delta'])), arb(fq(k['epsilon'])); Pc = [int(c) for c in k['polynomial']]
    n = len(Pc) - 1
    b = [sum(Pc[i] * Pc[j - i] for i in range(max(0, j - n), min(j, n) + 1)) for j in range(2 * n + 1)]
    dj = [d0 + j * e0 for j in range(2 * n + 1)]
    Z = sum((arb(b[j]) / dj[j] for j in range(2 * n + 1)), arb(0))
    c = [arb(b[j]) / (Z * dj[j]) for j in range(2 * n + 1)]          # h(x) = sum c_j d_j e^{-d_j x}
    return c, dj
def lap_affine(dd, x0, x1, A, D):    # int_{x0}^{x1} e^{-dd x} (A x - D) dx, x1 may be None (infinity) only when A = 0
    def prim(x): return -(-dd * x).exp() * ((A * x - D) / dd + A / dd ** 2)
    return (0 - prim(x0)) if x1 is None else (prim(x1) - prim(x0))
def selection_cells(segs, xmax=80.0):
    """cells of a piecewise selection of max(0, segs): breakpoints at segment ends and pairwise crossings (float-located; any
    selection is a valid lower bound); on each cell the function chosen is the max at the cell midpoint."""
    pts = set()
    for x0, x1, A, D in segs: pts.add(float(x0.mid())); pts.add(float(x1.mid()))
    fl = [(float(x0.mid()), float(x1.mid()), float(A.mid()), float(D.mid())) for x0, x1, A, D in segs]
    def val(i, x):
        x0, x1, A, D = fl[i]; xx = min(x, x1); return A * xx - D if x >= x0 else -1e99
    for i in range(len(fl)):
        for k in range(i + 1, len(fl)):
            for (u, w) in [(i, k)]:
                a0 = max(fl[u][0], fl[w][0]); a1 = xmax
                # crossing of two (possibly frozen) pieces: sample-and-bisect
                N = 400; prev = None
                for s_ in range(N + 1):
                    x = a0 + (a1 - a0) * s_ / N; dv = val(u, x) - val(w, x)
                    if prev is not None and (dv > 0) != (prev[1] > 0):
                        lo, hi = prev[0], x
                        for _ in range(60):
                            m = (lo + hi) / 2
                            if (val(u, m) - val(w, m) > 0) == (prev[1] > 0): lo = m
                            else: hi = m
                        pts.add((lo + hi) / 2)
                    prev = (x, dv)
    pts = sorted(p for p in pts if p < xmax)
    cells = []
    for a, b in zip(pts, pts[1:]):
        m = (a + b) / 2; best = None; bv = 0.0
        for i in range(len(fl)):
            v = val(i, m)
            if v > bv: bv, best = v, i
        cells.append((a, b, best))
    return cells, pts[-1]
def exactify(segs):
    """round each affine bound OUTWARD to exact endpoints (A down, D up; x0 up, x1 down), a valid lower bound: on its range the
    exact piece is <= the certified one, and the frozen tail value uses x1 rounded down (smaller value, still valid since the
    envelope is nondecreasing)."""
    out = []
    for x0, x1, A, D in segs:
        A_ = arb(A.lower()) if A.lower() > 0 else arb(A.lower()); D_ = arb(D.upper())
        out.append((arb(x0.upper()), arb(x1.lower()), A_, D_))
    return out
def lower_bound(segs, c, dj):
    segs = exactify(segs)
    cells, xlast = selection_cells(segs)
    tot = arb(0)
    for j in range(len(c)):
        acc = arb(0)
        for a, b, i in cells:
            if i is None: continue
            x0, x1, A, D = segs[i]
            lo, hi = arb(a), arb(b)
            # bb rigour fix: never integrate a piece before its proven start x0 (exact); below x0 use 0 (the envelope is >= 0)
            if hi <= x0: continue
            if lo < x0: lo = x0
            if hi <= x1: acc += lap_affine(dj[j], lo, hi, A, D)
            elif lo >= x1: acc += lap_affine(dj[j], lo, hi, arb(0), -(A * x1 - D))
            else: acc += lap_affine(dj[j], lo, x1, A, D) + lap_affine(dj[j], x1, hi, arb(0), -(A * x1 - D))
        # tail beyond xlast: the frozen maximum constant (valid: monotone envelope)
        frozen = max((A * x1 - D for x0, x1, A, D in segs), key=lambda z: z.lower())
        acc += lap_affine(dj[j], arb(xlast), None, arb(0), -frozen)
        tot += c[j] * dj[j] * acc
    return tot
