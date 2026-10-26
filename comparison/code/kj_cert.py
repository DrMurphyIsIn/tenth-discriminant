"""K(j) by certified quadrature of OUR I(k) (lead; bb G2 ACTION). I(k) = int_0^1 2a psi(k, a) da with psi's closed forms
(R0 part 3): for a >= 1-k, psi = (1-k) log(a/(1-k)) - k + tau (elementary, integrated exactly); for a < 1-k, psi = tau u + (1-tau) k log u - k
with u = u(a) the root of u - k = a u^(1-tau) in [k, 1]. Change variables a -> u (a = (u - k) u^(tau-1), monotone increasing for u in
[k, 1]), so int_0^{1-k} 2a psi da = int_k^1 2 a(u) psi(u) a'(u) du: an explicit elementary integrand, integrated rigorously with
acb.integral; then K(j) = int_0^j I(k) dk by acb.integral of the (k-)integrand (nested). Compared with v6.1's (29)."""
from flint import arb, acb, ctx, fmpq
ctx.prec = 128
tau = arb(fmpq(3, 10))
def I_of_k(k):
    k = arb(k) if not isinstance(k, arb) else k
    # part 1: a in [1-k, 1], psi = (1-k) log(a/(1-k)) - k + tau; int 2a[(1-k)(log a - log(1-k)) - k + tau] da, exact antiderivative
    def F1(a): return (1 - k) * (a * a * a.log() - a * a / 2 - a * a * (1 - k).log()) + (tau - k) * a * a
    p1 = F1(arb(1)) - F1(1 - k)
    # part 2: u in [k, 1], a(u) = (u - k) u^(tau - 1), a'(u) = u^(tau-1) + (tau - 1)(u - k) u^(tau - 2); psi = tau u + (1-tau) k log u - k
    def f2(u, _):
        a = (u - acb(k)) * u ** (acb(tau) - 1); ap = u ** (acb(tau) - 1) + (acb(tau) - 1) * (u - acb(k)) * u ** (acb(tau) - 2)
        ps = acb(tau) * u + (1 - acb(tau)) * acb(k) * u.log() - acb(k)
        return 2 * a * ps * ap
    p2 = acb.integral(f2, acb(k), acb(1)).real if k > 0 else acb.integral(f2, acb(fmpq(1, 10 ** 30)), acb(1)).real
    return p1 + p2
if __name__ == "__main__":
    print("I(0) =", I_of_k(arb(0)).str(20), " vs 2 tau^2/(2 tau + 1) =", (2 * tau ** 2 / (2 * tau + 1)).str(20))
    j = arb(fmpq(1, 9))
    # K(j) = int_0^j I(k) dk: I is smooth on [0, j]; integrate with acb.integral treating I(k) as a real-analytic function via a
    # Gauss-Legendre-free approach: nested acb.integral over the unit square in (k, u) after the change of variables
    def g(t, _):                      # t in [0, j]; inner integral evaluated pointwise (acb.integral needs analytic outer integrand)
        return acb(I_of_k(t.real))
    import mpmath as mp
    mp.mp.dps = 40
    Kq = mp.quad(lambda k: mp.mpf(I_of_k(arb(mp.nstr(k, 40))).mid().str(35, radius=False)), [0, 1 / mp.mpf(9)])
    print("K(1/9) (outer mpmath quad of certified inner I) =", mp.nstr(Kq, 25))

def K_bracket(N=3000):
    """Certified bracket for K(1/9): I decreasing (envelope theorem), so (j/N) sum_{i=1..N} I(ij/N).lower <= K <= (j/N) sum_{i=0..N-1} I(ij/N).upper.
    At k = 0 use the EXACT I(0) = 2 tau^2/(2 tau + 1) (bb K1: I_of_k(0) starts the u-integral at 1e-30)."""
    j = fmpq(1, 9); I0 = 2 * tau ** 2 / (2 * tau + 1)
    vals = [I0] + [I_of_k(arb(j * i / N)) for i in range(1, N + 1)]
    for i in range(N): assert vals[i + 1] < vals[i] or i == 0 and vals[1] < I0
    up = sum((arb(v.upper()) for v in vals[:-1]), arb(0)) * arb(j) / N
    lo = sum((arb(v.lower()) for v in vals[1:]), arb(0)) * arb(j) / N
    return arb(lo.lower()), arb(up.upper())
