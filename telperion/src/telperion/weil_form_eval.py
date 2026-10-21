"""Rigorous rational enclosures of the E8 Weil pairing (weil_form_enclosure backend).

conjecture1_proved = False.  This module does NOT prove RH.  It EVALUATES, with rigorous
Arb (python-flint) ball arithmetic, the pairing that the registry node
``RH_limit_explicit_formula`` (E8, `WeilExplicit`) identifies with the zero side:

    weilForm f  =  archSide f  -  primeSide f
                =  h_f(i/2) + h_f(-i/2)  -  f(0) log pi
                   + (1 / 2 pi) * integral_R h_f(r) * Re psi(1/4 + i r / 2) dr
                   -  sum_n  Lambda(n) / sqrt n * (f(log n) + f(-log n)),

for a CONCRETE test function `f` drawn from the registered E8 class (smooth, compactly
supported), and returns an outward-rounded RATIONAL enclosure `[lo, hi]` of its real part.

The cross-correlation entries of a `k x k` Weil-Gram matrix are the same object with
`f = f_ij := g_i (star) conj(g_j(-.))`, so one code path serves both.

WHAT IS EVALUATED, AND WHY EACH PIECE IS RIGOROUS
--------------------------------------------------
Test class.  `g(u) = amp * P(t) * B(t)` with `t = (u - c) / w` and
`B(t) = exp(-1/(1 - t^2))` on `|t| < 1`, `B = 0` outside -- the standard bump, scaled by
`w > 0`, shifted by `c`, optionally multiplied by a real polynomial `P`.  This is
`C_c^infinity` (the registered `WeilExplicit.IsWeilTest` class) and REAL-valued, which is
what makes every simplification below legitimate.  COMPACT SUPPORT IS NOT OPTIONAL: for a
merely Schwartz `g` the prime side DIVERGES (`sum_{n <= e^R} Lambda(n) n^{-1/2} ~ 2 e^{R/2}`;
E8 design memo section 2.2), so a non-compact spec is REFUSED, never enclosed.

Laplace/Fourier identities used (real `g_i`, `g_j`; `f_ij(x) = int g_i(t) g_j(t - x) dt`):

  * `F_ij(z) := int f_ij(u) e^{z u} du = G_i(z) * G_j(-z)`, `G(z) := int g(u) e^{z u} du`.
    Hence the two pole terms are `weilKernel f 0 = G_i(-1/2) G_j(1/2)` and
    `weilKernel f 1 = G_i(1/2) G_j(-1/2)` -- NO convolution quadrature is needed for them.
  * `h_ij(r) := F_ij(i r) = h_i(r) h_j(-r)` where `h(r) = int g(u) e^{i r u} du`.  For REAL
    `g_j`, `h_j(-r) = conj(h_j(r))` on the real axis, so the archimedean integrand equals
    `h_i(r) conj(h_j(r)) Re psi(...)` there -- but written as `h_i(r) h_j(-r)` it is ENTIRE
    in `r`, which is what Arb's path integrator requires.  (Writing `conj` or `.real` inside
    the integrand destroys analyticity and silently invalidates the enclosure; the `Re psi`
    factor is likewise passed as the analytic
    `(psi(1/4 + i r/2) + psi(1/4 - i r/2)) / 2`, which agrees with `Re psi` for real `r`.)
  * `f_ij(0) = int g_i g_j`, and `f_ij(+-log n)` is one short convolution quadrature per
    prime power; `Lambda(n) = 0` off the prime powers, and the support of `f_ij` is bounded,
    so the prime side is a FINITE sum (the compact-support payoff).

Interior cut.  `B` is not analytic at `t = +-1`, so every `u`-quadrature runs over
`|t| <= 1 - delta` and the two cut collars are bounded by the monotone envelope
`|B(t)| <= exp(-1/(2 delta))` there (`1 - t^2 <= 2 delta`); with `delta = 1/256` that is
`e^{-128} < 2e-56` per collar, and the collar contribution is added to the enclosure radius
rather than dropped.

Archimedean tail.  `int_{|r| > T}` is bounded, not truncated:

  * `|h_ij(r)| <= L_N / |r|^N` with `L_N := ||f_ij^{(N)}||_1 <= ||g_i^{(N)}||_1 * ||g_j||_1`
    (N-fold integration by parts, then Young); `||g^{(N)}||_1 <= 2 w^{1-N} amp * S_N` with
    `S_N` a TIGHT rigorous bound on `sup |(P B)^{(N)}|` computed by ball-grid evaluation of
    the exact symbolic derivative `Q_N(t) / (1 - t^2)^{2N} * B(t)` (sympy for `Q_N`, Arb for
    the grid), the collar `1 - t^2 <= 1/(64 N)` handled by the monotone envelope
    `(sum |coef Q_N|) * s^{-2N} e^{-1/s}`.
  * `|Re psi(1/4 + i y)| <= log(|y| + 2) + 4.4` for ALL real `y`.  Proof (from
    `psi(z) = -gamma + sum_{n>=0} (1/(n+1) - 1/(n+z))`, `a_n = n + 1/4`,
    `Re 1/(n+z) = a_n/(a_n^2 + y^2)`): splitting at `M = ceil(|y|) + 1`, the terms below `M`
    give at most `H_M <= 1 + log M`, and above `M`
    `1/(n+1) - a_n/(a_n^2+y^2) <= 1/a_n - a_n/(a_n^2+y^2) = y^2/(a_n(a_n^2+y^2)) <= y^2/a_n^3`,
    summing to `<= y^2 / (2 (M - 3/4)^2) <= 1/2`; so `Re psi <= log(|y|+2) + 1`.  Downward,
    each term is `>= 1/(n+1) - 1/a_n = -(3/4)/((n+1)(n+1/4))`, whose total is `<= 3.75`, so
    `Re psi >= -gamma - 3.75 >= -4.33`.  The bound is ALSO re-verified numerically on a
    dyadic Arb sweep before any box is handed out (the refuse-to-emit anchor below).
  * `log(r+2) + 4.4 <= C_T sqrt r` for `r >= T`, `C_T = (log(T+2) + 4.4)/sqrt T`, because
    `(log(r+2)+4.4)/sqrt r` is decreasing on `r > 0` (its derivative is negative iff
    `2r/(r+2) < log(r+2) + 4.4`, and the left side is `< 2 < 4.4`).

  Together: `(1/2pi) int_{|r|>T} <= (1/2pi) * 2 L_N C_T T^{3/2 - N} / (N - 3/2)`, added to the
  enclosure radius.

EXTERNAL ANCHORS (refuse-to-emit gates, mirroring `bragg_coeff`)
-----------------------------------------------------------------
Before any box is returned: (a) the `Re psi` bound is re-checked on a dyadic Arb sweep;
(b) `Lambda(2), Lambda(3), Lambda(4) = log 2, log 3, log 2` against rational windows;
(c) `B` values at `t = 0` and `t = 1/2` against published rational windows.  A normalisation
or index bug ABORTS here rather than emitting.

The Arb ball arithmetic is the documented NON-KERNEL trust seam, identical in kind to the
Li ladder and `bragg_coeff`: the emitted Lean carries the enclosure as a NAMED HYPOTHESIS and
the kernel proves only its consequence.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Sequence

# python-flint is imported INSIDE the functions that need it: `telperion/__init__` imports
# emit_weil_form_enclosure unconditionally for sensitivity-registry completeness, so nothing
# at module level here may require flint (same idiom as bragg_coeff).

# Interior cut for the non-analytic bump endpoints (see module docstring).
CUT_DELTA = Fraction(1, 256)
# Default archimedean quadrature half-width and number of integrations by parts.
DEFAULT_T = 1024
DEFAULT_NBY = 5
DEFAULT_PREC = 100

_LOG2_LO, _LOG2_HI = Fraction("0.6931"), Fraction("0.6932")
_LOG3_LO, _LOG3_HI = Fraction("1.0986"), Fraction("1.0987")
# B(0) = e^{-1} = 0.3678794411..., B(1/2) = e^{-4/3} = 0.2635971381...
_B0_LO, _B0_HI = Fraction("0.36787"), Fraction("0.36788")
_BH_LO, _BH_HI = Fraction("0.26359"), Fraction("0.26360")


@dataclass(frozen=True)
class WeilTestSpec:
    """One concrete member of the E8 test class: `g(u) = amp * P(t) * B(t)`, `t = (u-c)/w`.

    `poly` are the coefficients of `P` in ASCENDING powers of `t` (default `P = 1`).  The
    support is `[c - w, c + w]`; `is_compactly_supported` is True by construction, and the
    certificate layer REFUSES anything for which it is False (the PNT growth trap)."""

    label: str
    width: Fraction = Fraction(1)
    center: Fraction = Fraction(0)
    amp: Fraction = Fraction(1)
    poly: tuple = (Fraction(1),)
    is_compactly_supported: bool = True

    def __post_init__(self):
        if self.width <= 0:
            raise ValueError(f"WeilTestSpec REFUSED: width must be > 0, got {self.width}")
        if not self.poly:
            raise ValueError("WeilTestSpec REFUSED: empty polynomial factor")

    @property
    def support(self) -> tuple:
        return (self.center - self.width, self.center + self.width)


@dataclass(frozen=True)
class GaussianSpec:
    """`g(u) = exp(-(u-c)^2 / (2 a^2))` -- the E8 design memo's section-4 cross-check function.

    DELIBERATELY NOT compactly supported: it is inside the Guinand class (where the identity
    also holds) but OUTSIDE the registered E8 class, so it is usable ONLY for the numerical
    zero-side/prime-side cross-check report and is REFUSED by the certificate layer."""

    label: str
    a: Fraction
    center: Fraction = Fraction(0)
    is_compactly_supported: bool = False


@dataclass(frozen=True)
class WeilFormBox:
    """An outward-rounded rational enclosure `[lo, hi]` of `Re weilForm f_ij`, with the four
    term magnitudes kept for the report (a sign/factor error shows up as a term of the wrong
    order, exactly the E8 memo's section-4 diagnostic)."""

    i: int
    j: int
    label_i: str
    label_j: str
    lo: Fraction
    hi: Fraction
    terms: dict = field(default_factory=dict)

    @property
    def width(self) -> Fraction:
        return self.hi - self.lo


# --------------------------------------------------------------------------------------
# Rigorous sup bounds for the derivatives of the bump profile (sympy symbolic + Arb grid).
# --------------------------------------------------------------------------------------

_SUP_CACHE: dict = {}


def _profile_deriv_sup(poly: tuple, n: int, *, prec_bits: int = 120, grid: int = 3000) -> Fraction:
    """Rigorous upper bound on `sup_{|t|<1} |(P(t) B(t))^{(n)}|`, `B(t) = exp(-1/(1-t^2))`.

    The exact `n`-th derivative is `Q(t)/(1-t^2)^{2n} * B(t)` with `Q` a polynomial (sympy).
    On `s = 1 - t^2 >= s0 := 1/(64 n)` the bound comes from an Arb ball grid in `s`; on the
    collar `s < s0` from the monotone envelope `(sum |coef Q|) s0^{-2n} e^{-1/s0}` (monotone
    increasing in `s` there because `s0 << 1/(2n)`)."""
    key = (tuple(poly), n, prec_bits, grid)
    if key in _SUP_CACHE:
        return _SUP_CACHE[key]
    import sympy as sp
    from flint import arb, ctx

    t = sp.symbols("t")
    P = sum(sp.Rational(c) * t**k for k, c in enumerate(poly))
    B = sp.exp(-1 / (1 - t**2))
    if n == 0:
        expr = sp.cancel(sp.simplify(P))
        num, _den = sp.fraction(sp.together(expr))
        m = 0
    else:
        d = sp.cancel(sp.simplify(sp.diff(P * B, t, n) / B))
        num, _den = sp.fraction(sp.together(d))
        m = 2 * n
    Q = sp.Poly(sp.expand(num), t)
    coeffs = [sp.Rational(c) for c in Q.all_coeffs()]          # descending
    A = sum(abs(c) for c in coeffs)

    old = ctx.prec
    ctx.prec = prec_bits
    try:
        s0 = sp.Rational(1, 64 * max(n, 1))
        env = sp.Rational(A) * s0 ** (-m) * sp.exp(-1 / s0)     # symbolic collar envelope
        env_f = Fraction(sp.nsimplify(0))
        env_f = Fraction(str(sp.N(env, 30)))
        acoef = [arb(c.p) / arb(c.q) for c in coeffs]
        s_lo = float(s0)
        best = arb(0)
        for k in range(grid):
            s = arb(s_lo + (1 - s_lo) * k / grid).union(arb(s_lo + (1 - s_lo) * (k + 1) / grid))
            tt = (1 - s).sqrt()
            qp = arb(0)
            qm = arb(0)
            for c in acoef:
                qp = qp * tt + c
                qm = qm * (-tt) + c
            qb = arb(max(qp.abs_upper(), qm.abs_upper()))
            val = qb * ((1 / s) ** m if m else arb(1)) * (-1 / s).exp()
            u = arb(val.abs_upper())
            if u.abs_upper() > best.abs_upper():
                best = u
        grid_bound = _arb_upper_fraction(best)
    finally:
        ctx.prec = old
    out = grid_bound + env_f
    _SUP_CACHE[key] = out
    return out


def _arb_upper_fraction(x) -> Fraction:
    """Exact `Fraction` upper bound of an Arb ball (via `man_exp`, no decimal round-trip)."""
    from flint import arb
    b = arb(x.abs_upper())
    man, exp = b.mid().man_exp()
    mid = Fraction(int(man)) * (Fraction(2) ** int(exp))
    rman, rexp = b.rad().man_exp()
    rad = Fraction(int(rman)) * (Fraction(2) ** int(rexp))
    return mid + rad


def _l1_deriv_bound(spec: WeilTestSpec, n: int) -> Fraction:
    """`||g^{(n)}||_1 <= 2 w^{1-n} |amp| sup |(P B)^{(n)}|` (support length `2w`, chain rule)."""
    sup = _profile_deriv_sup(spec.poly, n)
    return 2 * abs(spec.amp) * (spec.width ** (1 - n)) * sup


# --------------------------------------------------------------------------------------
# The Arb evaluator.
# --------------------------------------------------------------------------------------

def _flint():
    from flint import acb, arb, ctx
    return acb, arb, ctx


def _prime_power_lambda(n: int):
    """`(p, Lambda(n))` support test: return the base prime if `n = p^k`, else None."""
    if n < 2:
        return None
    m, p = n, 2
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            return p if m == 1 else None
        p += 1
    return n


def self_check(*, prec_bits: int = DEFAULT_PREC) -> None:
    """External anchors; raises before any box is produced if a normalisation is off."""
    acb, arb, ctx = _flint()
    old = ctx.prec
    ctx.prec = prec_bits
    try:
        # (a) |Re psi(1/4 + i y)| <= log(|y|+2) + 4.4 on a dyadic sweep.
        y = arb(1) / 8
        for _ in range(40):
            z = acb(arb(1) / 4, y / 2)
            w = acb(arb(1) / 4, -y / 2)
            re = ((z.digamma() + w.digamma()) / 2).real
            bound = (y + 2).log() + arb(44) / 10
            if not (arb(re.abs_upper()) < bound):
                raise ValueError(
                    f"weil_form_eval ANCHOR FAILED: |Re psi(1/4+i*{y})| exceeds "
                    f"log(|y|+2)+4.4 -- the archimedean tail bound is invalid")
            y = y * 2
        # (b) von Mangoldt anchors.
        for n, lo, hi in ((2, _LOG2_LO, _LOG2_HI), (3, _LOG3_LO, _LOG3_HI),
                          (4, _LOG2_LO, _LOG2_HI)):
            p = _prime_power_lambda(n)
            lam = arb(p).log()
            if not (arb(lam.lower()) > arb(lo.numerator) / arb(lo.denominator)
                    and arb(lam.upper()) < arb(hi.numerator) / arb(hi.denominator)):
                raise ValueError(f"weil_form_eval ANCHOR FAILED: Lambda({n}) outside window")
        # (c) bump profile values.
        for tv, lo, hi in ((arb(0), _B0_LO, _B0_HI), (arb(1) / 2, _BH_LO, _BH_HI)):
            b = (-(1 / (1 - tv * tv))).exp()
            if not (arb(b.lower()) > arb(lo.numerator) / arb(lo.denominator)
                    and arb(b.upper()) < arb(hi.numerator) / arb(hi.denominator)):
                raise ValueError("weil_form_eval ANCHOR FAILED: bump profile value off")
    finally:
        ctx.prec = old


def _make_g(spec: WeilTestSpec):
    """Return `(g, lo, hi)`: the Arb callable and the CUT integration endpoints in `u`."""
    acb, arb, ctx = _flint()
    w = acb(spec.width.numerator) / acb(spec.width.denominator)
    c = acb(spec.center.numerator) / acb(spec.center.denominator)
    amp = acb(spec.amp.numerator) / acb(spec.amp.denominator)
    pc = [acb(Fraction(p).numerator) / acb(Fraction(p).denominator) for p in spec.poly]

    def g(u):
        t = (u - c) / w
        P = acb(0)
        for cc in reversed(pc):
            P = P * t + cc
        return amp * P * (-(1 / (1 - t * t))).exp()

    d = acb(CUT_DELTA.numerator) / acb(CUT_DELTA.denominator)
    lo_f = float(spec.center - spec.width * (1 - CUT_DELTA))
    hi_f = float(spec.center + spec.width * (1 - CUT_DELTA))
    return g, c - w * (1 - d), c + w * (1 - d), lo_f, hi_f


def _collar_bound(spec: WeilTestSpec, *, weight: Fraction) -> Fraction:
    """Upper bound on the magnitude discarded by the two interior cut collars of one
    `u`-quadrature, times `weight` (a bound on the rest of the integrand there)."""
    # |B| <= exp(-1/(2 delta)) on the collar; |P| <= sum|coef|; collar length 2 * w * delta each.
    from flint import arb, ctx
    old = ctx.prec
    ctx.prec = 80
    try:
        e = (-(1 / (2 * arb(CUT_DELTA.numerator) / arb(CUT_DELTA.denominator)))).exp()
        env = _arb_upper_fraction(e)
    finally:
        ctx.prec = old
    Pabs = sum(abs(Fraction(c)) for c in spec.poly)
    return 2 * (2 * spec.width * CUT_DELTA) * abs(spec.amp) * Pabs * env * weight


def enclose_weil_form_entry(
    spec_i: WeilTestSpec,
    spec_j: WeilTestSpec,
    *,
    i: int = 0,
    j: int = 0,
    prec_bits: int = DEFAULT_PREC,
    arch_T: int = DEFAULT_T,
    n_byparts: int = DEFAULT_NBY,
    run_self_check: bool = True,
) -> WeilFormBox:
    """Rigorous rational enclosure of `Re weilForm f_ij`, `f_ij = g_i (star) conj(g_j(-.))`.

    REFUSES a non-compactly-supported spec (the prime side would diverge -- E8 memo 2.2) and
    `n_byparts < 2` (the archimedean tail bound needs `N > 3/2`)."""
    for s in (spec_i, spec_j):
        if not getattr(s, "is_compactly_supported", False):
            raise ValueError(
                f"weil_form_eval REFUSED: test function '{s.label}' is not compactly "
                f"supported -- primeSide diverges for a merely Schwartz g "
                f"(sum_{{n<=e^R}} Lambda(n) n^{{-1/2}} ~ 2 e^{{R/2}}; E8 design memo 2.2)")
    if n_byparts < 2:
        raise ValueError(f"weil_form_eval REFUSED: need n_byparts >= 2, got {n_byparts}")
    if run_self_check:
        self_check(prec_bits=prec_bits)

    acb, arb, ctx = _flint()
    old = ctx.prec
    ctx.prec = prec_bits
    try:
        gi, ai, bi, ai_f, bi_f = _make_g(spec_i)
        gj, aj, bj, aj_f, bj_f = _make_g(spec_j)

        def G(g, a, b, z):
            return acb.integral(lambda u, _an: g(u) * (acb(z) * u).exp(), a, b)

        half = acb(1) / 2
        # pole terms: weilKernel f 0 + weilKernel f 1 = G_i(-1/2)G_j(1/2) + G_i(1/2)G_j(-1/2)
        Gi_p, Gi_m = G(gi, ai, bi, half), G(gi, ai, bi, -half)
        Gj_p, Gj_m = G(gj, aj, bj, half), G(gj, aj, bj, -half)
        poles = Gi_m * Gj_p + Gi_p * Gj_m
        # f(0) log pi
        ov_lo, ov_hi = max(ai_f, aj_f), min(bi_f, bj_f)
        f0 = (acb.integral(lambda t, _an: gi(t) * gj(t), acb(ov_lo), acb(ov_hi))
              if ov_hi > ov_lo else acb(0))
        logpi_term = f0 * acb(arb.pi().log())

        def h(g, a, b, r):
            return acb.integral(lambda u, _an: g(u) * (acb(0, 1) * r * u).exp(), a, b)

        def repsi(r):
            z = acb(1) / 4 + (r / 2) * acb(0, 1)
            w = acb(1) / 4 - (r / 2) * acb(0, 1)
            return (z.digamma() + w.digamma()) / 2

        def integrand(r, _an):
            return h(gi, ai, bi, r) * h(gj, aj, bj, -r) * repsi(r)

        total = acb(0)
        edges = [-arch_T]
        e = arch_T
        while e > 1:
            edges.append(-e // 2)
            e //= 2
        edges = sorted(set(edges + [0] + [-x for x in edges]))
        for a_, b_ in zip(edges, edges[1:]):
            total += acb.integral(integrand, acb(a_), acb(b_))
        arch = total / (2 * arb.pi())

        # prime side (finite: supp f_ij = [c_i - c_j - w_i - w_j, c_i - c_j + w_i + w_j])
        lo_x = spec_i.center - spec_j.center - spec_i.width - spec_j.width
        hi_x = spec_i.center - spec_j.center + spec_i.width + spec_j.width
        reach = max(abs(lo_x), abs(hi_x))
        import math
        n_max = int(math.floor(math.exp(float(reach)))) + 1

        def f_at(x: float):
            """f_ij(x) = int g_i(t) g_j(t - x) dt over the overlap of the two cut supports."""
            a_ = max(ai_f, aj_f + x)
            b_ = min(bi_f, bj_f + x)
            if b_ <= a_:
                return acb(0)
            return acb.integral(
                lambda t, _an: gi(t) * gj(t - acb(x)), acb(a_), acb(b_))

        prime = acb(0)
        for n in range(2, n_max + 1):
            p = _prime_power_lambda(n)
            if p is None:
                continue
            lam = acb(arb(p).log())
            ln = math.log(n)
            prime += lam / acb(arb(n).sqrt()) * (f_at(ln) + f_at(-ln))

        value = poles - logpi_term + arch - prime
        val_re = value.real

        # --- rigorous additions to the radius -------------------------------------------
        # (1) archimedean tail beyond |r| > arch_T
        L = _l1_deriv_bound(spec_i, n_byparts) * _l1_bound(spec_j)
        CT = _c_T(arch_T, prec_bits=prec_bits)
        N = Fraction(n_byparts)
        tail = (Fraction(2) * L * CT * (Fraction(arch_T) ** (Fraction(3, 2) - N))
                / (N - Fraction(3, 2)))
        tail_arch = tail * _inv_two_pi_upper(prec_bits=prec_bits)
        # (2) interior cut collars: pole terms, f(0), prime side, archimedean integrand.
        ei = _exp_weight(spec_i)
        ej = _exp_weight(spec_j)
        collar = (_collar_bound(spec_i, weight=ei * _l1_bound(spec_j))
                  + _collar_bound(spec_j, weight=ej * _l1_bound(spec_i)))
        collar = collar * Fraction(8)   # the four quadrature families, both collars each

        lo = _lower_fraction(val_re) - tail_arch - collar
        hi = _upper_fraction(val_re) + tail_arch + collar
        terms = {
            "poles": _mid_str(poles.real),
            "logpi": _mid_str(logpi_term.real),
            "arch": _mid_str(arch.real),
            "prime": _mid_str(prime.real),
            "arch_tail_bound": str(float(tail_arch)),
            "collar_bound": str(float(collar)),
            "n_max": str(n_max),
            "arch_T": str(arch_T),
            "n_byparts": str(n_byparts),
        }
        return WeilFormBox(i=i, j=j, label_i=spec_i.label, label_j=spec_j.label,
                           lo=lo, hi=hi, terms=terms)
    finally:
        ctx.prec = old


def _l1_bound(spec: WeilTestSpec) -> Fraction:
    """`||g||_1 <= 2 w |amp| sup|P B|`."""
    return _l1_deriv_bound(spec, 0)


def _exp_weight(spec: WeilTestSpec) -> Fraction:
    """`max |e^{u/2}|` over the support -- the largest weight any quadrature applies."""
    lo, hi = spec.support
    from flint import arb, ctx
    old = ctx.prec
    ctx.prec = 80
    try:
        return _arb_upper_fraction((arb(max(abs(lo), abs(hi)).numerator)
                                   / arb(max(abs(lo), abs(hi)).denominator) / 2).exp())
    finally:
        ctx.prec = old


def _c_T(T: int, *, prec_bits: int) -> Fraction:
    from flint import arb, ctx
    old = ctx.prec
    ctx.prec = prec_bits
    try:
        return _arb_upper_fraction(((arb(T) + 2).log() + arb(44) / 10) / arb(T).sqrt())
    finally:
        ctx.prec = old


def _inv_two_pi_upper(*, prec_bits: int) -> Fraction:
    from flint import arb, ctx
    old = ctx.prec
    ctx.prec = prec_bits
    try:
        return _arb_upper_fraction(1 / (2 * arb.pi()))
    finally:
        ctx.prec = old


def _lower_fraction(x) -> Fraction:
    man, exp = x.mid().man_exp()
    mid = Fraction(int(man)) * (Fraction(2) ** int(exp))
    rman, rexp = x.rad().man_exp()
    rad = Fraction(int(rman)) * (Fraction(2) ** int(rexp))
    return mid - rad


def _upper_fraction(x) -> Fraction:
    man, exp = x.mid().man_exp()
    mid = Fraction(int(man)) * (Fraction(2) ** int(exp))
    rman, rexp = x.rad().man_exp()
    rad = Fraction(int(rman)) * (Fraction(2) ** int(rexp))
    return mid + rad


def _mid_str(x) -> str:
    return x.str(12, radius=False)


def enclose_weil_gram(
    specs: Sequence[WeilTestSpec], **kwargs
) -> dict:
    """`{(i, j): WeilFormBox}` for every `i <= j` of the `k x k` Weil-Gram matrix."""
    out = {}
    for i, si in enumerate(specs):
        for j, sj in enumerate(specs):
            if j < i:
                continue
            out[(i, j)] = enclose_weil_form_entry(
                si, sj, i=i, j=j, run_self_check=(i == 0 and j == 0), **kwargs)
    return out


# --------------------------------------------------------------------------------------
# The non-Lean numerical cross-check the E8 design memo ran (section 4), re-run with Arb.
# --------------------------------------------------------------------------------------

def gaussian_cross_check(
    spec: GaussianSpec, *, n_zeros: int = 60, n_primes: int = 5000, prec_bits: int = 200
) -> dict:
    """Zero side vs `archSide - primeSide` for a GAUSSIAN `g` (Guinand class, NOT the E8
    class): the memo's section-4 agreement run, reproduced with rigorous Arb zeta zeros.

    Returns a REPORT dict (never a certificate): a Gaussian is not compactly supported, so
    `weil_form_enclosure_certificate` refuses it and nothing here reaches Lean."""
    acb, arb, ctx = _flint()
    old = ctx.prec
    ctx.prec = prec_bits
    try:
        a = arb(spec.a.numerator) / arb(spec.a.denominator)
        c = arb(spec.center.numerator) / arb(spec.center.denominator)
        # h(r) = a sqrt(2 pi) e^{i c r} e^{-a^2 r^2/2}; analytic continuation in r is entire.
        def hfun(r):
            return (a * (2 * arb.pi()).sqrt()) * (acb(0, 1) * c * r).exp() \
                * (-(acb(a) * acb(a)) * r * r / 2).exp()

        # zero side: sum over the first n_zeros ordinates, both signs (all simple).
        zero_side = acb(0)
        for n in range(1, n_zeros + 1):
            rho = acb.zeta_zero(n)
            gam = rho.imag
            zero_side += hfun(acb(gam)) + hfun(acb(-gam))
        # arch side
        poles = hfun(acb(0, 1) / 2) + hfun(acb(0, -1) / 2)
        g0 = (-((c * c) / (2 * a * a))).exp()
        logpi = acb(g0) * acb(arb.pi().log())

        def repsi(r):
            z = acb(1) / 4 + (r / 2) * acb(0, 1)
            w = acb(1) / 4 - (r / 2) * acb(0, 1)
            return (z.digamma() + w.digamma()) / 2

        T = 40
        arch_int = acb(0)
        edges = [-T, -20, -10, -5, -2, -1, 0, 1, 2, 5, 10, 20, T]
        for lo_, hi_ in zip(edges, edges[1:]):
            arch_int += acb.integral(lambda r, _an: hfun(r) * repsi(r), acb(lo_), acb(hi_))
        arch = poles - logpi + arch_int / (2 * arb.pi())
        # prime side
        import math
        prime = acb(0)
        for n in range(2, n_primes + 1):
            p = _prime_power_lambda(n)
            if p is None:
                continue
            ln = arb(n).log()
            gv = (-((ln - c) * (ln - c)) / (2 * a * a)).exp() \
                + (-((-ln - c) * (-ln - c)) / (2 * a * a)).exp()
            prime += acb(arb(p).log() / arb(n).sqrt() * gv)
        rhs = arch - prime
        diff = zero_side - rhs
        return {
            "label": spec.label,
            "a": str(spec.a),
            "center": str(spec.center),
            "n_zeros": n_zeros,
            "n_primes": n_primes,
            "zero_side": _mid_str(zero_side.real),
            "rhs": _mid_str(rhs.real),
            "abs_difference": str(float(abs(diff.real.mid()))),
            "poles": _mid_str(poles.real),
            "arch_integral": _mid_str((arch_int / (2 * arb.pi())).real),
            "prime_side": _mid_str(prime.real),
        }
    finally:
        ctx.prec = old


def round_outward(lo: Fraction, hi: Fraction, sig: int = 12) -> tuple:
    """Round `[lo, hi]` OUTWARD to `sig` significant figures: `lo` down, `hi` up.

    Arb radii read out exactly through `man_exp` are dyadic with enormous numerators; the
    emitted Lean literal must stay short.  Widening the box only ever WEAKENS the certified
    consequence, so a survivor is still rigorous -- the same directed-rounding discipline as
    `examples/li_positivity/generate_bragg_floor.py`."""
    return _round_sig(lo, sig, down=True), _round_sig(hi, sig, down=False)


def _round_sig(x: Fraction, sig: int = 12, *, down: bool) -> Fraction:
    """Nearest `sig`-significant-figure fraction on the given side of `x` (down => <= x)."""
    if x == 0:
        return Fraction(0)
    neg = x < 0
    ax = Fraction(-x) if neg else Fraction(x)
    exp = 0
    ten = Fraction(10)
    while ax * ten**exp < 10**(sig - 1):
        exp += 1
    while ax * ten**exp >= 10**sig:
        exp -= 1
    scaled = ax * ten**exp
    base = Fraction(scaled.numerator // scaled.denominator, 1) / ten**exp
    step = ten**(-exp)
    if neg:
        mag = base + step if (down and base != ax) else base
        return -mag
    return base + step if (not down and base != ax) else base
