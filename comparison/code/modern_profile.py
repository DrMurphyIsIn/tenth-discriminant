"""CMP-3 S2/S2c (lead; data double-transcribed: reader 1 and bb's reader 2 agree, S2_READER2_bb.md 6a9943f5): the modern prime profile.
eps_low(m) >= sup_{x >= e^m} (x - theta(x))/x, from BKLNW Table 13 (best k; the C9-failing D4[1e8,1e9) EXCLUDED), Büthe (1.6) for
1427 <= x <= 1e19 (the printed 1423 fails C9 on [1423, 1427)), and BKLNW Table 14 k = 0 (for all x > X0). Every value is bumped up one unit
in its last digit (BKLNW p. 26).
- **Argument (bb: SOUND).** Every bound is nonincreasing in x on its validity set, and BREAKS holds every point where the applicable set
  changes. So on each piece the min of the applicable bounds is nonincreasing, and the sup over [e^m, inf) is attained at a piece's
  LEFT END.
- **Rigour (bb R-a/R-b, v1).** Each piece is evaluated at its exact left end, with its applicable set chosen from the piece's interior.
  The start is the LOWER end of m. Breakpoints are exact (integers, or e^{l0} as Arb balls). D_k/(log x)^k is evaluated with the lower
  end of log x. Every operation is in Arb, and the returned value is an upper bound.
- **v2 (bb S2 Add.1).** Duplicate breakpoints are dropped, so there are no zero-length pieces (conservative before; now exact).
- **c_up.** theta(x) <= (1 + 1.93379e-8) x for all x (BKLNW Cor 2.1, bumped).
- **Mertens (S2c).** A(x) - log x - E >= -eps_low(log x) - M2b/log(max(x, 1e19)), with M2b = 3.7980e-5 (BKLNW Table 15 row 19 log 10,
  M2 = 3.7979e-5, bumped; bb C2)."""
import json, math
from flint import arb, fmpq
T = json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'data', 'transcription_theta_bounds.json')))
def bump(s):
    m, e = s.lower().split('e'); d = len(m.split('.')[1]) if '.' in m else 0
    return fmpq(int(m.replace('.', '')), 10 ** d) * fmpq(10) ** int(e) + fmpq(10) ** (int(e) - d)
def logx(s):                                          # exact x given as a decimal string -> log as an Arb ball
    v = float(s); return arb(max(int(round(v)), 2)).log()
LOG1427, LOG1e19 = arb(1427).log(), arb(10 ** 19).log()
T13 = []
for r in T['BKLNW_Table13']['rows']:
    Ds = [bump(x) for x in r['D']]
    if r['a'] == '1e8': Ds[4] = None                  # C9 failure: source typo (arXiv v2)
    T13.append((logx(r['a']), logx(r['b']), Ds))
T14 = []
for r in T['BKLNW_Table14_k0']['rows']:
    l0 = LOG1e19 if 'log' in r['logX0'] else arb(fmpq(*(map(int, r['logX0'].split('.')) if '.' not in r['logX0'] else (int(r['logX0'].replace('.', '')), 10 ** len(r['logX0'].split('.')[1])))))
    T14.append((l0, bump(r['m0'])))
M2B = arb(fmpq(37980, 10 ** 9))
BREAKS = [z for la, lb, _ in T13 for z in (la, lb)] + [LOG1427, LOG1e19] + [l0 for l0, _ in T14]
def _applicable(Lint, Lleft):
    """bounds applicable on the piece whose interior point is Lint (a float), evaluated at its left end Lleft (Arb, lower end used)."""
    Llo = arb(Lleft.lower()); c = []
    for la, lb, Ds in T13:
        if la.upper() <= Lint < lb.lower():
            c += [arb(D) / Llo ** k for k, D in enumerate(Ds) if D is not None]
    if LOG1427.upper() <= Lint <= LOG1e19.lower(): c.append(arb(fmpq(195, 100)) * (-Llo / 2).exp())
    for l0, m0 in T14:
        if Lint > l0.upper(): c.append(arb(m0))
    return c
def eps_low(m):
    m0 = arb(arb(m).lower())
    cand = sorted([b for b in BREAKS if b.lower() > m0.upper()], key=lambda z: z.mid())
    lefts = [m0]
    for b in cand:                                   # bb (S2 Add.1): drop zero-length pieces (duplicate breakpoints)
        if not (b.lower() <= lefts[-1].upper() and lefts[-1].lower() <= b.upper()): lefts.append(b)
    best = None
    for i, u in enumerate(lefts):
        if u.upper() >= 25000: break
        nxt = lefts[i + 1] if i + 1 < len(lefts) else u + 1
        Lint = float(((u + nxt) / 2).mid())            # interior point: selects the applicable set only
        c = _applicable(Lint, u)
        if not c: raise ValueError(f"no bound applies near log x = {Lint}")
        v = min(c, key=lambda z: z.upper()); v = arb(v.upper())
        if best is None or v.upper() > best.upper(): best = v
    return best
def d_low(m): return 1 - eps_low(m)
C_UP = 1 + arb(fmpq(193379, 10 ** 13))
def c_up(m): return C_UP
def A_corr(L):
    return eps_low(L) + M2B / max(arb(arb(L).lower()), LOG1e19, key=lambda z: z.lower())
