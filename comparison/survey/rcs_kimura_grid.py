"""CMP-1 group G, the piecewise normal form (lead, 2026-10-25; per bb REVIEW_CMP1_RCS Add.1 f692a0b9, G1).

Input (the author's Lean, NOT replayed by us): Kimura's grid, cln-imq-2k v1.4 computations/lean_grid.txt (md5 pinned below), with
313 intervals [l0_i, l1_i] and constants c_i (the c_target column, an exact rational): for a primitive real chi of conductor q with
log q in [l0_i, l1_i], every real zero beta has (1 - beta) log q >= c_i. The tail is log q >= 10000 with c = 203/20000.
(Lean: gap_i : B4.GapOn c_i l0_i l1_i in B4Certificates.lean, per bb; the statements are to be quoted verbatim in the cmp-G memo.)

Combined with Lemma Z(kappa, D) (rcs_zero.py): for h = 1 and d >= D, 1 - beta < kappa/sqrt d, so (1 - beta) log d < kappa log(d)/sqrt(d).
Since log x/sqrt x decreases for x > e^2, on interval i the largest value over d >= D is at l = max(log D, l0_i). So if
kappa * l * e^(-l/2) < c_i for every interval with l1_i > log D (and for the tail), no class-number-one d >= D exists: D0 = D.
"""
import hashlib, os, re, sys
from flint import arb, fmpq, ctx
ctx.prec = 300
HERE = os.path.dirname(os.path.abspath(__file__))
RCS_ZERO = os.path.join(HERE, 'rcs_zero.py')                                 # bb N3: md5 pinned
assert hashlib.md5(open(RCS_ZERO, 'rb').read()).hexdigest() == '5046bbdb5f335fa71cb1850c9ca88962'
sys.path.insert(0, HERE)
import contextlib, io
with contextlib.redirect_stdout(io.StringIO()):   # rcs_zero prints its own table on import
    from rcs_zero import lemma_ok
# Kimura's grid is NOT shipped: pass the path of a checkout of Kimura's cln-imq-2k v1.4 (md5s of the two files read are pinned).
if len(sys.argv) < 2: sys.exit("usage: python3 rcs_kimura_grid.py <path to Kimura's cln-imq-2k-1.4 checkout>")
KIMURA = sys.argv[1]
GRID = os.path.join(KIMURA, 'computations', 'lean_grid.txt')
raw = open(GRID, 'rb').read()
assert hashlib.md5(raw).hexdigest() == '38017689a841943faadd674c522d80eb'
def fq(s):
    n, _, d = s.partition('/')
    return fmpq(int(n), int(d) if d else 1)
def q(s): return arb(fq(s))
iv = []
ivq = []
for line in raw.decode().splitlines():
    m = re.match(r'\s*(\d+)\s+\[(.*)\]\s*$', line)
    if m:
        f = [x.strip() for x in m.group(2).split(',')]
        iv.append((int(m.group(1)), q(f[0]), q(f[1]), q(f[8])))   # fields: l0, l1, k, j, a, ropt, m, cval, c_target
        ivq.append((fq(f[0]), fq(f[1]), fq(f[8])))
assert len(iv) == 313 and all(ivq[k][1] == ivq[k + 1][0] for k in range(312)) and ivq[312][1] == 10000   # bb N2: exact fmpq
TAIL = (arb(10000), arb(fmpq(203, 20000)))
def check(D, kappa, scale=1):
    ok, margin = lemma_ok(arb(kappa), D)
    if not ok: return False, None
    k, L = arb(kappa), arb(D).log()
    worst = None
    for i, l0, l1, c in iv + [(314, TAIL[0], arb(10 ** 9), TAIL[1])]:
        if l1 <= L: continue          # bb N1: skip only when certainly below
        l = l0 if l0 > L else L
        v = k * l * (-l / 2).exp()
        r = (c * scale) / v
        if not (v < c * scale): return False, (i, r)
        if worst is None or r < worst[1]: worst = (i, r)
    return True, worst
def least(scale=1, kappas=("1.912", "1.915", "1.918", "1.92", "1.93", "1.95", "2")):
    lo, hi = 17.0, 23.0           # bisection on log D over a grid of step 1e-4 in log D
    best = None
    for _ in range(40):
        mid = (lo + hi) / 2
        D = int(arb(mid).exp().floor().unique_fmpz())
        good = None
        for k in kappas:
            ok, w = check(D, k, scale)
            if ok: good = (k, w); break
        if good: hi, best = mid, (D, good)
        else: lo = mid
        if hi - lo < 1e-4: break
    return best
best = least()
D, (k, (i, r)) = best
print(f"grid md5 38017689 (313 intervals + tail). CERTIFIED BOUND (not the least): h = 1 implies d < {D} (log D = {arb(D).log().str(8)}), kappa = {k};")
print(f"   tightest interval i = {i}, c_i/value = {r.str(6)}")
ok, _ = check(D, k); assert ok
b2 = least(scale=fmpq(1, 2))
print(f"F2 control (every c_i halved): least certified D = {b2[0]} (log {arb(b2[0]).log().str(8)}), which must exceed {D}: {b2[0] > D}")

# bb R1/R2: Kimura's chain theorems chain_i : B4.GapFrom minc_i l_i (B4Certificates.lean 1bca4c25), i.e. the (c, q0) normal form
# with q0 = e^l. chain_i's constant = min of c_j over j >= i (tail included); checked here against the grid.
def chain(i):
    cs = [c for (_, _, c) in ivq[i - 1:]] + [fmpq(203, 20000)]
    return min(cs), ivq[i - 1][0]
def D0_normal_form(c, l0, kappas=("1.912", "1.915", "1.918", "1.92", "1.93", "1.95", "2")):
    """least certified D (bisection in log D, step 1e-5) such that Lemma Z(kappa, D) holds and, for all x >= max(D, e^l0),
    kappa log x/sqrt x < c; returns D0 = max(e^l0, that D) as a certified bound."""
    c, L0 = arb(c), arb(l0)
    def good(logD):
        D = int(arb(logD).exp().floor().unique_fmpz()) + 1
        for k in kappas:
            ok, _ = lemma_ok(arb(k), D)
            if not ok: continue
            l = arb(logD) if arb(logD) > L0 else L0
            if arb(k) * l * (-l / 2).exp() < c: return D, k
        return None
    lo, hi = 15.0, 25.0
    best = None
    for _ in range(60):
        mid = (lo + hi) / 2
        g = good(mid)
        if g: hi, best = mid, g
        else: lo = mid
        if hi - lo < 1e-5: break
    return best
LEAN = os.path.join(KIMURA, 'lean', 'B4Certificates.lean')   # bb L1: read the cited statement
lean_src = open(LEAN, 'rb').read()
assert hashlib.md5(lean_src).hexdigest() == '1bca4c2523bc5abf99dbafaeb9688071'
def lean_chain(i):
    m = re.search(r'theorem chain_%d : B4\.GapFrom \((\d+)/(\d+) : ℝ\) \((\d+)/(\d+) : ℝ\) :=' % i, lean_src.decode())
    a, b, c_, d_ = map(int, m.groups())
    return fmpq(a, b), fmpq(c_, d_)
for i in (58, 59):
    c, l0 = chain(i)
    assert (c, l0) == lean_chain(i), (i, (c, l0), lean_chain(i))
    print(f"chain_{i}: grid-derived (c, l0) == the Lean statement in B4Certificates.lean (1bca4c25)")
    D, k = D0_normal_form(c, l0)
    q0 = arb(l0).exp()
    bound = "c-bound" if arb(D) > q0 else "q0-bound"
    Dfin = max(D, int(q0.upper().floor().unique_fmpz()) + 1)
    print(f"chain_{i} = GapFrom({c}, {l0}) [l0 = {arb(l0).str(8)}]: Lemma Z at kappa {k}; {bound}; CERTIFIED BOUND: d < {Dfin} (log {arb(Dfin).log().str(8)})")
