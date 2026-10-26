"""CMP-2 R0 code, module 3: per-row constant K, affine bounds, eight stages, the envelope L(x) (lead, 2026-10-25).
Derivations: the paper, Sections 5 and 6 (our derivation notes are not published). The epsilon-level formulas are
v6.1's printed mathematics, (17)-(34) of its paper (credited; read from the PDF), each re-derived in our notes in structure.
Every rounding below is conservative. DIFFERENCES from v6.1: (a) A(R) lower bound from RS (3.21), constant -E = 1.33258..
instead of 1.334 (flag OURS_A); (b) G_s in OUR closed form (eps/2) log(delta) OUTSIDE the (t - eps) factor (R0 part 3 query).
Inputs (PARAMETERS ONLY): t, C, tau, gamma, stages, band ends, rows."""
import json, math
from flint import arb, fmpq, ctx
import primes as P, sieve as SV
ctx.prec = 320
# The method constants of the determinant argument (twinheterodox v0.6.1, credited): t = 3/64, C = 27/64, tau = 3/10.
# gamma is set per band from the band file (only beta/4 <= gamma is needed).
t, Cc, tau = arb(fmpq(3, 64)), arb(fmpq(27, 64)), arb(fmpq(3, 10))
gam = arb(fmpq(3, 10))
def fq(s): return fmpq(*map(int, s.split('/'))) if '/' in s else fmpq(int(s))
def Ap(p, tt): return (1 / (2 * arb(p) ** 2) - tt / (2 * p) + tt * tt / 6) if p * tt <= 1 else 1 / (6 * tt * arb(p) ** 3)
def pos(x): return x if x > 0 else (arb(0) if x < 0 else arb(0).union(x) if False else (x if x.lower() >= 0 else arb(0) if x.upper() <= 0 else arb(0)))
def Kfun(j):
    A = 2 * tau
    return (j * 2 * tau ** 2 / (2 * tau + 1) - (1 - tau) * (j ** 2 / (2 * A) - j ** 3 / (3 * (A - 1)) + j ** 4 / (12 * (A - 2))
            - 2 * j ** (A + 2) / (A * (A - 1) * (A - 2) * (A + 1) * (A + 2))) + j / 2 - 3 * j ** 2 / 4 + (1 - j) ** 2 / 2 * (1 - j).log() + j ** 3 / 6 - j ** 4 / 24)
USE_KCERT = True
# Certified K(j) (lead 2026-10-25; bb G2 ACTION): I(k) = int 2a psi(k,a) da is DECREASING in k (envelope theorem: d psi/dk = log((u-k)/a) <= 0),
# so K(1/9) <= right... the left Riemann sum: K(1/9) <= (j/N) sum_{i<N} I(i j/N) with certified I (kj_cert.py, N = 3000) = K_HI below, and
# K(j) <= K(1/9) + (j - 1/9) I(0) for j >= 1/9.
import kj_cert as _KJ
_KLO, _KUP = _KJ.K_bracket(3000)                           # computed and certified at import (bb K1), not hard-coded
K_HI = _KUP
assert K_HI >= arb('0.0078016499')
def Kcert(j): return K_HI + (j - arb(fmpq(1, 9))) * 2 * tau ** 2 / (2 * tau + 1)
def row_constants(Q0, Q1, a2, OURS_A=True, OURS_GS=True):
    M = arb(2) ** a2; eps = 1 / M; logM = M.log()
    vp = arb(Q1).sqrt() / 2; rhop = (1 + vp * vp).sqrt() / 2
    rstar = (Cc * M * vp / arb.pi()).sqrt(); e = rhop / rstar
    nu = Cc * (1 + 2 * e) ** 2; g = (Cc / (2 * arb.pi())).log() / 2 + (1 + e).log()
    b0 = (t - eps) / nu
    j = arb(fmpq(1, 9)) + eps; jst = j - b0 / 2 + b0 / M
    alpha = (1 - t) / 2 - jst; beta = 1 + t - 2 * jst
    Bc = (1 - tau) * j * (1 - j.log()); I0 = 2 * tau ** 2 / (2 * tau + 1)
    # D*: the lattice-cell error 5e/(3(1+e)) is PER DERIVATIVE ORDER, and the order sum over k < J (J/R <= j) multiplies it by j,
    # exactly like B (lead's derivation 2026-10-25, R0 part 3 fix; the frozen f447ee39 omitted this j, a conservative slip).
    # bb M2 (entry 6): the order sum is R[K + j(B + 5e/(3(1+e)))] + I(0) + B, so after normalising by 2/(R^2 S) the I(0) + B part
    # is (2 nu R/S)(I(0) + B)/R <= (2 nu/(t - eps)) eps (I(0) + B): INSIDE the factor (v2 had it outside: NON-conservative)
    Dst = -3 * tau / 2 + 2 * nu / (t - eps) * ((Kcert(j) if USE_KCERT else Kfun(j)) + j * (Bc + 5 * e / (3 * (1 + e))) + eps * (I0 + Bc)) - 2 * Bc
    delta = j * Cc / (t - eps) * ((1 + 2 * e) ** 2 + e / (2 + e)) - 1
    assert 0 < delta < 1 and delta >= e
    core = arb(1) / 4 - delta + 3 * delta ** 2 / 4 - delta ** 2 / 2 * delta.log()
    Gs = ((t - eps) * core + eps / 2 * delta.log()) if OURS_GS else (t - eps) * (core + eps / 2 * delta.log())
    Gs = Gs if Gs > 0 else arb(0)
    H = 21; aH, thH, WH = P.small_prime_consts(H, t)
    BH = P.B_H(H)
    pairs = SV.split_pairs(Q0, Q1)
    K2 = sum((arb(SV.Qform(Q1, a, b)).log() / arb(SV.Qform(Q1, a, b)) ** 2 for a, b in pairs), arb(0)) + arb(Q1).log() / arb(Q1) ** 2
    c = P.c_up(logM)
    mf = (M / 33).log(); ds, cs = P.d_low(mf), P.c_up(mf)
    Aflo = (arb(33).log() - sum((arb(1) / k for k in range(1, 34)), arb(0)) + 1) / 2
    Bflo = (sum((arb(1) / k for k in range(1, 33)), arb(0)) - arb(33).log()) / 2
    Gfloor = Bflo * ds - Aflo * cs; Gfloor = Gfloor if Gfloor > 0 else arb(0)
    small = [p for p in P._P if fmpq(p) < fmpq(Q0, 4)]
    Gsmall = arb(0); Gres = arb(0); Gcoup = arb(0)
    for p in small:
        lp = arb(p).log(); acc = arb(0); ee = 2
        while arb(p) ** ee < M:
            v = (b0 - eps) / arb(p) ** ee - 2 * eps; acc += v if v > 0 else 0; ee += 1
        v = (t - eps) / arb(p) ** 2 - 3 * eps; acc += v if v > 0 else 0
        Gsmall += lp * acc
        v = 2 * Ap(p, t) / p - (2 + arb(2) / p ** 3) * eps; Gres += lp * v if v > 0 else 0
        v = (1 - arb(1) / p) * (Ap(p, t) - (1 + arb(1) / p ** 2) * eps - jst) - eps; Gcoup += 2 * lp * v if v > 0 else 0
    Aconst = (-P.E_RS) if OURS_A else arb(fmpq(1334, 1000))
    Kbase = (aH - WH + c + (BH - K2) / (3 * (t - eps)) + beta * g + Dst + 2 * logM / M - Gs + 2 * thH / M + logM / ((t - eps) * M)
             + 2 * (t * M * M).log() / M + Aconst + 1 / (2 * logM) - Gfloor - Gsmall - Gres - Gcoup)
    assert beta / 4 < gam
    return dict(M=M, eps=eps, b0=b0, alpha=alpha, beta=beta, Kbase=Kbase)
def envelope_eval(segs, x):
    """segs: list of (x0, x1, A, D) affine bounds A x - D on [x0, x1], frozen at x1 beyond; returns max(0, all) at x (arb)."""
    best = arb(0)
    for x0, x1, A, D in segs:
        if x < x0: continue
        xx = x if x <= x1 else x1
        v = A * xx - D
        if v > best: best = v
    return best
def build(band, OURS_A=True, OURS_GS=True, stages=None):
    Q0, Q1 = band['q0'], band['q1']; rows = band['rows']; stages = band['stages'] if stages is None else stages
    consts = {r['a']: row_constants(Q0, Q1, r['a'], OURS_A, OURS_GS) for r in rows}
    Phi_segs = []                                  # band-uniform Phi for the feedback (stage 0: Phi = 0)
    for st in range(stages + 1):
        segs = []
        for r in rows:
            k = consts[r['a']]; kap = arb(fq(r['k']))
            M, eps, b0 = k['M'], k['eps'], k['b0']
            if Phi_segs:
                x1p = (M * (b0 - eps)).log(); x2p = (M * (t - eps)).log()
                gfb = (b0 - eps) * envelope_eval(Phi_segs, x1p)
                # split-row factorial: (S/R) T_split(S) >= (t - eps)(Phi(log(M(t - eps))) - log Q0/Q0)_+, since T_split = T minus the
                # ramified term (log q/q) f(q/S) <= log Q0/Q0 (lead's derivation 2026-10-25; the frozen f447ee39 subtracted log Q0/Q0
                # OUTSIDE the factor (t - eps), a conservative slip)
                v = (t - eps) * (envelope_eval(Phi_segs, x2p) - arb(Q0).log() / Q0)
                gfb += v if v > 0 else 0
            else:
                gfb = arb(0)
            K = k['Kbase'] - gfb
            A = k['alpha']; D = k['alpha'] * kap.log() + k['beta'] / 4 * arb(Q0).log() + K
            x0 = r['a'] * arb(2).log() + kap.log(); x1 = r['b'] * arb(2).log() + kap.log()
            segs.append((x0, x1, A, D))
        if st < stages:
            shift = gam * (arb(Q1) / Q0).log()
            Phi_segs = [(x0, x1, A, D + shift) for (x0, x1, A, D) in segs]
    return segs
