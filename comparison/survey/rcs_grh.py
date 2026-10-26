"""CMP-1 GRH group (lead, 2026-10-25). Label (bb H1): CONDITIONAL: no real zero of L(s, chi_{-d}) in (1/2 + 1/800, 1), which GRH implies. Check of twinheterodox 698514's 'q <= 200 under GRH' (via Stopple p. 868's
Chowla-Selberg statement 'h(-d) = 1 and d/a^2 > 200 contradict GRH'; Stopple 698534 asked whether 200 suffices; twinheterodox
698578: 'd/a^2 >= 200 works').
The certificate needs only L(sigma0, chi) >= 0 at sigma0 = 1/2 + 1/800, i.e. no real zero in (sigma0, 1) (then L > 0 on (sigma0, 1]
since L(1) > 0), so zeta_K(sigma0) <= 0. With rcs_edge's M and B (validated
CS normalisation; h = 1, w = 2, d > 4), if M(sigma, d) - B(sigma, d) > 0 for some sigma in (1/2, 1), d is excluded. M increases
in d at fixed sigma (zeta(2 sigma - 1) < 0 there), B decreases, so d >= ceil(d_M(sigma)) is excluded for each sigma. The best
bound is the inf over sigma of d_M(sigma); sigma -> 1/2+ is optimal on a SAMPLED grid (bb H4: sampled, not proved; this
bears on optimality only). Closed form of the limit (bb H2): 64 pi^2 e^(-2 gamma) = (8 pi e^(-gamma))^2 = 199.12077...,
which bb recalls as the Chowla-Selberg Epstein constant k = sqrt(d)/(2a) > 4 pi e^(-gamma) = 7.0555 (to be read at source)."""
from flint import arb, fmpq, ctx
ctx.prec = 300
def C(s): return arb(2) ** (2 * s - 1) * arb.pi().sqrt() * (s - arb(1) / 2).gamma() / s.gamma()
def M(s, d): return (2 * s).zeta() + C(s) * (2 * s - 1).zeta() * arb(d) ** (arb(1) / 2 - s)
def B(s, d):
    x = arb.pi() * arb(d).sqrt()
    pref = arb(2) ** (s + arb(3) / 2) * arb.pi() ** s / (s.gamma() * arb(d) ** (s / 2 - arb(1) / 4))
    return pref * (arb.pi() / (2 * x)).sqrt() * (-x).exp() / (1 - 2 * (-x).exp())
def dM(s): return (-C(s) * (2 * s - 1).zeta() / (2 * s).zeta()) ** (1 / (s - arb(1) / 2))
best = None
for k in range(1, 400):
    s = arb(fmpq(1, 2)) + arb(fmpq(k, 800))
    v = dM(s)
    if best is None or v < best[1]: best = (s, v, k)
s, v, k = best
D = int(v.upper().floor().unique_fmpz()) + 1
m, b = M(s, D), B(s, D)
print(f"min over the SAMPLED sigma grid (step 1/800): sigma = 1/2 + {k}/800 = {s.str(8)}, d_M = {v.str(12)}")
print(f"certified at D = {D}: M = {m.str(8)}, B <= {b.str(4)}, M - B > 0: {(m - b) > 0}  => under GRH, h = 1 and d > 4 imply d <= {D - 1}")
for kk in (40, 100, 200, 300):
    t = arb(fmpq(1, 2)) + arb(fmpq(kk, 800)); print(f"   sigma = {t.str(6)}: d_M = {dM(t).str(10)}")
lim = 64 * arb.pi() ** 2 * (-2 * arb.const_euler()).exp()
print(f"closed form 64 pi^2 e^(-2 gamma) = {lim.str(15)}")
for e in (fmpq(1, 10**4), fmpq(1, 10**6)):        # bb H3: the eps = 1e-6 claim, now in the file
    t = arb(fmpq(1, 2)) + arb(e); v = dM(t); DD = int(v.upper().floor().unique_fmpz()) + 1
    print(f"   eps = {e}: d_M = {v.str(12)}; at D = {DD}: M - B > 0: {(M(t, DD) - B(t, DD)) > 0}")
