"""Lorentzian / Hodge-Riemann certificates — Telperion's NON-SEPARABLE vocabulary.

Every crux tool we certified so far is separable or scalar: a per-node potential,
a per-prime valuation, a univariate interlacing.  The Brualdi-Goldwasser
obstruction (the N(11,11) collectivity) is invisible to any function of a scalar
projection -- it lives in the MIXED second derivatives across different children.

Lorentzian polynomials (Branden-Huh; real-stable => Lorentzian, so the
Heilmann-Lieb matching polynomial qualifies) carry exactly that structure: their
Hessian at a point of the positive cone has signature (1, n-1) -- ONE positive
eigenvalue -- and the Hodge-Riemann relation is the REVERSE Cauchy-Schwarz

    (vᵀH w)²  ≥  (vᵀH v)(wᵀH w)      for v in the positive cone,

a genuinely non-separable inequality (it couples w_i, w_j for i ≠ j).  It is
certifiable: the gap `wᵀM w`, M = (Hv)(Hv)ᵀ − (vᵀH v)·H, is PSD, and a PSD
rational form is a sum of squares (LDLᵀ).  So a Hodge-Riemann certificate is an
SOS certificate -- Telperion's polynomial-nonnegativity strength, lifted from
the univariate (interlacing) to the multivariate (Lorentzian) case.

HONEST SCOPE: this certifies the Hodge-index inequality of a GIVEN Lorentzian
form.  It does NOT by itself close the crux -- the missing object must ALSO be
integral (exact at the tie) and tight, an arithmetic Hodge-Riemann relation that
no framework yet supplies (see height_ledger).  This builds the one genuinely
untested handle so it can be engaged, not a proof.
"""
from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


def hessian(poly: sp.Expr, xs) -> sp.Matrix:
    return sp.hessian(poly, xs)


def real_sign(val, tol: float = 1e-25, prec: int = 50) -> int:
    """Sign (-1, 0, +1) of a value KNOWN to be real but possibly delivered by sympy in casus-irreducibilis
    radical form -- a real irreducible-cubic root written with radicals of complex numbers, so its imaginary
    part is a formal artifact that cancels but which `sp.sign`/`sp.simplify` cannot cheaply resolve (and
    `simplify` can hang).  Ported imaginary-part-handling capability: fast exact paths (rational / declared
    real), then a high-precision numeric evaluation of the REAL part with the imaginary artifact chopped.

    Correct for eigenvalues of a symmetric (Hermitian) matrix, which are guaranteed real; a genuinely zero
    eigenvalue is an exact rational char-poly root and evaluates to ~0 far below `tol`."""
    if getattr(val, "is_rational", False) and val.is_rational:
        return 0 if val == 0 else (1 if val > 0 else -1)
    if getattr(val, "is_zero", False):
        return 0
    r = complex(sp.N(val, prec)).real                # real part; imaginary artifact chopped
    return 0 if abs(r) < tol else (1 if r > 0 else -1)


def signature(H: sp.Matrix) -> tuple[int, int, int]:
    """(n_pos, n_zero, n_neg) of a symmetric matrix, robust to casus-irreducibilis radical eigenvalues
    (via `real_sign`).  A symmetric matrix has real eigenvalues; the sign of each is read exactly when
    cheap and numerically (real part) otherwise."""
    pos = zero = neg = 0
    for val, mult in H.eigenvals().items():
        s = real_sign(val)
        if s > 0:
            pos += mult
        elif s < 0:
            neg += mult
        else:
            zero += mult
    return int(pos), int(zero), int(neg)


def is_lorentzian_form(H: sp.Matrix) -> bool:
    """The Hodge-index signature (1, n-1): exactly one positive eigenvalue."""
    pos, _, _ = signature(H)
    return pos == 1


def _sos_of_psd(M: sp.Matrix, ws):
    """PSD rational M -> [(d_i, linear_form_i)] with wᵀM w = Σ d_i · form_i²,
    via LDLᵀ (rational).  d_i >= 0 for PSD."""
    L, D = M.LDLdecomposition(hermitian=False)
    w = sp.Matrix(ws)
    forms = (L.T * w)
    terms = []
    for i in range(M.rows):
        d = sp.nsimplify(D[i, i]) if not D[i, i].is_number else D[i, i]
        if d != 0:
            terms.append((d, sp.expand(forms[i])))
    # verify exactly
    assert sp.expand((w.T * M * w)[0] - sum(d * f**2 for d, f in terms)) == 0
    return terms


@dataclass(frozen=True)
class HodgeRiemannCertificate:
    """The Hodge-Riemann (reverse-Cauchy-Schwarz) inequality of a Lorentzian
    form H at a positive-cone vector v, certified by SOS."""

    name: str
    poly: sp.Expr          # the Lorentzian polynomial
    xs: tuple              # its variables
    v: tuple               # a timelike vector (vᵀH v > 0)
    ws: tuple              # fresh variables for the inequality

    def hessian(self) -> sp.Matrix:
        return hessian(self.poly, list(self.xs))

    def check(self) -> bool:
        H = self.hessian()
        if not is_lorentzian_form(H):
            return False
        v = sp.Matrix(self.v)
        return (v.T * H * v)[0] > 0

    def lean(self) -> str:
        H = self.hessian()
        v, w = sp.Matrix(self.v), sp.Matrix(self.ws)
        vHv = sp.expand((v.T * H * v)[0])
        M = sp.expand(H * v) * sp.expand(H * v).T - vHv * H
        Q = sp.expand((v.T * H * w)[0] ** 2 - vHv * (w.T * H * w)[0])
        terms = _sos_of_psd(M, list(self.ws))

        def _lean(e):
            return sp.printing.sstr(e).replace("**", "^")

        sos = " + ".join(f"({_lean(d)}) * ({_lean(f)})^2" for d, f in terms)
        binder = " ".join(f"{s}" for s in self.ws)
        return (
            f"-- {self.name}: Hodge-Riemann / reverse Cauchy-Schwarz for a Lorentzian\n"
            f"-- form (signature (1,n-1)): (vᵀHw)² - (vᵀHv)(wᵀHw) = SOS ≥ 0.  This is\n"
            f"-- the NON-SEPARABLE inequality (couples distinct children).\n"
            f"theorem {self.name} : ∀ {binder} : ℝ, (0:ℝ) ≤ {_lean(Q)} := by\n"
            f"  intro {binder}\n"
            f"  have hsos : ({_lean(Q)} : ℝ) = {sos} := by ring\n"
            f"  rw [hsos]; positivity\n"
        )
