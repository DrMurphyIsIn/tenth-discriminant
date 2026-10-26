"""CMP-2 section 8.1 obligation (lead, 2026-10-25): on Y = log(q/Q0) in [0, Ymax], the upper main sum U_main(Y) = sum_j c_j F_j H_j(Y)
must have U_main'(Y) < -gamma (so that lower - gamma Y - U(q) >= gap(Q0)). H_j(Y) = F0 e^{-aY}(L0 + Y + kap)/(2(z2 + F0 e^{-aY})), a = s - 1/2.
Method: Taylor model of U' at the cell centre (arb_series: exact point coefficients), remainder by a Cauchy estimate on the complex disk
|Y - Yc| <= rho (acb), |U^{(m)}| <= m! S Hmax / rho^m with S = sum |c_j| F_j, Hmax = max_j max_disk |H_j|."""
from flint import arb, acb, arb_series, acb_series, fmpq, ctx
import outer as O, math
ctx.prec = 640
def Hparts(q0, d):
    s = 1 + d; v0 = arb(q0).sqrt() / 2
    C = arb.pi().sqrt() * (s - arb(1) / 2).gamma() / s.gamma()
    z21, dz21 = O.zeta_d(2 * s - 1); z2, dz2 = O.zeta_d(2 * s)
    F0 = C * v0 ** (1 - 2 * s) * z21
    kap = s.digamma() - (s - arb(1) / 2).digamma() - 2 * dz21 / z21 + 2 * dz2 / z2
    return F0, z2, (arb(q0) / 4).log() + kap, s - arb(1) / 2
def U_series(c, dj, q0, Yc, n):
    Ys = arb_series([Yc, 1], prec=n + 2); tot = arb_series([0], prec=n + 2)
    for j in range(len(c)):
        F0, z2, L0k, a = Hparts(q0, dj[j])
        E = (-a * Ys).exp(); Fq = E * F0
        H = Fq * (Ys + L0k) / ((Fq + z2) * 2)
        tot += H * (c[j] * O.Fw(dj[j]))
    return tot
def Hmax_disk(c, dj, q0, Yc, rho):
    Yb = acb(arb(Yc), 0) + acb(arb(0, rho), arb(0, rho))           # complex box containing the disk
    m = arb(0)
    for j in range(len(c)):
        F0, z2, L0k, a = Hparts(q0, dj[j])
        Fq = acb(F0) * (acb(-a) * Yb).exp(); H = Fq * (Yb + acb(L0k)) / ((Fq + acb(z2)) * 2)
        m = max(m, abs(H).upper(), key=lambda z: z.upper())
    return m
def check_band(band_kernel_c, dj, q0, q1, gamma, n=24, rho=fmpq(1, 2)):
    Ymax = (arb(q1) / q0).log(); Yc = Ymax / 2; hw = Ymax / 2
    ser = U_series(band_kernel_c, dj, q0, Yc, n)
    coeffs = [ser[k] for k in range(n + 2)]                        # U(Yc + t) = sum coeffs[k] t^k
    dcoef = [coeffs[k + 1] * (k + 1) for k in range(n)]            # U'(Yc + t) polynomial part, degree n-1
    S = sum((abs(cc) * O.Fw(d) for cc, d in zip(band_kernel_c, dj)), arb(0))
    Hm = Hmax_disk(band_kernel_c, dj, q0, Yc, arb(rho))
    r = arb(rho)
    # remainder of U' after degree n-1: sum_{k>=n} |U^{(k+1)}(Yc)|/k! hw^k <= sum_{k>=n} (k+1) S Hm hw^k / r^{k+1}
    # bb entry 12: poles of H_j at |Im Y| = pi/a; assert the disk radius stays clear
    amax = max(dj[j] + arb(1) / 2 for j in range(len(dj)))
    assert r < arb.pi() / amax - arb(fmpq(1, 10)), "Cauchy radius too close to the poles of H"
    x = hw / r; assert x < 1
    # exact tail: sum_{k>=n} (k+1) x^k = x^n ((n+1) - n x)/(1 - x)^2;  |U^{(k+1)}(Yc)|/k! <= (k+1) S Hm / r^(k+1)
    rem = S * Hm / r * x ** n * ((n + 1) - n * x) / (1 - x) ** 2
    tb = arb(0, hw.upper())
    poly = arb(0)
    for cc in reversed(dcoef): poly = poly * tb + cc
    Uprime = poly + arb(0, rem.upper())
    return Uprime, rem, (Uprime < -gamma)
def check_band_cells(c, dj, q0, q1, gamma, ncells=8, n=24, rho=fmpq(1, 2)):
    """section 8.1 over ncells equal cells of [0, Ymax], each with its own Taylor model and Cauchy remainder (same method as
    check_band, recentred at each cell's midpoint)."""
    Ymax = (arb(q1) / q0).log(); S = sum((abs(cc) * O.Fw(d) for cc, d in zip(c, dj)), arb(0)); r = arb(rho)
    amax = max(dj[j] + arb(1) / 2 for j in range(len(dj)))
    assert r < arb.pi() / amax - arb(fmpq(1, 10))
    worst = None; allok = True
    for i in range(ncells):
        Yc = Ymax * (2 * i + 1) / (2 * ncells); hw = Ymax / (2 * ncells)
        ser = U_series(c, dj, q0, Yc, n); dcoef = [ser[k + 1] * (k + 1) for k in range(n)]
        Hm = Hmax_disk(c, dj, q0, Yc, r); x = hw / r; assert x < 1
        rem = S * Hm / r * x ** n * ((n + 1) - n * x) / (1 - x) ** 2
        tb = arb(0, hw.upper()); poly = arb(0)
        for cc in reversed(dcoef): poly = poly * tb + cc
        Up = poly + arb(0, rem.upper())
        ok = Up < -gamma; allok &= bool(ok)
        if worst is None or Up.upper() > worst.upper(): worst = Up
    return worst, allok
