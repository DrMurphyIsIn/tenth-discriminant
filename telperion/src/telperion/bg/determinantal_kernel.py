"""Probe (physics transfer #3): the Brualdi-Goldwasser object as a determinantal-kernel (free-fermion) object.

Free fermions form a DETERMINANTAL POINT PROCESS: every correlation is a determinant of one projection
kernel `K`.  The determinant couples points irreducibly (non-separable), and on a lattice the kernel is
integer-indexed -- the honest realization of "a discrete Gaussian that couples points."  BG already carries
the fermion side: Girardeau duality gives `per(L)/prod(deg) = prod_{lambda>0}(1+lambda^2) = |det(I+iN)|`, a
FUNCTIONAL DETERMINANT (`girardeau.py`, `spectral.py`).  This probe asks whether that determinantal / kernel
structure LOCALIZES the tie.

FINDING (NEGATIVE for localization; the object is right-shaped but generic).
For near-stars `N(0,s)` the normalized adjacency `N = D^{-1/2} A D^{-1/2}` has the RIGID spectrum
`{0, +-1, +-1/sqrt(2) (multiplicity s-1)}` (char poly of `D^{-1}A` is `t(t-1)(t+1)(2t^2-1)^{s-1}`) -- the SAME
eigenvalue SET for every `s`, only the `+-1/sqrt(2)` multiplicity scaling with the arm count.  Hence the
Girardeau determinant is the clean geometric closed form

    per(L)/prod(deg) = prod_{lambda>0}(1+lambda^2) = 2 * (3/2)^(s-1),

a generic geometric sequence in which the tie `s=5` (value `81/8`) is entirely unremarkable.  The determinantal
kernel is a genuine non-separable determinant of an integer-derived operator (the right SHAPE), but the tie is
NOT a kernel/projection resonance -- no eigenvalue crosses, no rank collapses at `s=5`.

WHY (same unified reason as the SUSY-index probe).  The tie is the ARITHMETIC balance
`(64/621)^n (prod a)^11 = 1` of the `(64/621)^n` weight against this (rooted) algebraic growth; the
determinantal object is purely SPECTRAL/geometric and carries no `(64/621)` arithmetic, so it cannot see the
tie.  Archimedean/geometric determinants do not localize an arithmetic resonance -- only the 23-adic carrier
does.  `conjecture1_proved = False`.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr


def girardeau_determinant(n, edges) -> Fr:
    """`per(L)/prod(deg) = prod_{lambda>0}(1+lambda^2) = |det(I+iN)|` -- the free-fermion functional
    determinant (exact Fraction, via the monomer-dimer `matching_free_energy.rho`; equals the spectral
    product by Girardeau duality).  Non-separable (a determinant couples all modes)."""
    from .matching_free_energy import rho
    return rho(n, edges)


def near_star_determinant_closed_form(s: int) -> Fr:
    """Closed form of the Girardeau determinant on the near-star `N(0,s)`: `2 * (3/2)^(s-1)` -- a generic
    geometric sequence (tie `s=5` -> `81/8`, unremarkable)."""
    return Fr(2) * Fr(3, 2) ** (s - 1)


def normalized_spectrum_multiplicities(n, edges):
    """The multiset of `D^{-1}A` eigenvalues as `{rounded eigenvalue: multiplicity}` (same spectrum as the
    symmetric normalized adjacency `N`).  For near-stars this is `{0:1, 1:1, -1:1, +-1/sqrt2: s-1}`."""
    import numpy as np
    A = np.zeros((n, n))
    for a, b in edges:
        A[a, b] = 1
        A[b, a] = 1
    deg = A.sum(1)
    M = np.diag(1 / deg) @ A
    ev = np.linalg.eigvals(M).real
    out = {}
    for v in ev:
        key = round(float(v), 4)
        out[key] = out.get(key, 0) + 1
    return out


@dataclass(frozen=True)
class DeterminantalKernelProbe:
    """Physics-transfer probe #3: does the free-fermion determinantal-kernel object localize the BG tie?
    Verifies the Girardeau object is a genuine non-separable determinant with a clean geometric closed form
    and a RIGID generic spectrum, so the tie is not a kernel resonance.  `check()` certifies this, NOT BG."""

    near_star_s: tuple = (2, 3, 4, 5, 6)

    def girardeau_matches_closed_form(self) -> bool:
        """`per(L)/prod(deg) = 2*(3/2)^(s-1)` exactly for every near-star -- a determinant with a clean
        geometric closed form."""
        from .frustration_free import near_star_edges
        for s in self.near_star_s:
            n, e = near_star_edges(s)
            if girardeau_determinant(n, e) != near_star_determinant_closed_form(s):
                return False
        return True

    def spectrum_generic_across_near_stars(self) -> bool:
        """The normalized-adjacency eigenvalue SET is `{0, 1, -1, 1/sqrt2, -1/sqrt2}` for EVERY near-star
        (only the +-1/sqrt2 multiplicity scales) -- so the tie is not spectrally distinguished."""
        from .frustration_free import near_star_edges
        r = round(1 / 2 ** 0.5, 4)
        want = {0.0, 1.0, -1.0, r, -r}
        for s in self.near_star_s:
            n, e = near_star_edges(s)
            mult = normalized_spectrum_multiplicities(n, e)
            if set(mult) != want:
                return False
            if mult.get(r) != s - 1 or mult.get(-r) != s - 1:      # only these scale with the arm count
                return False
        return True

    def determinant_does_not_localize_tie(self) -> bool:
        """The determinant `2*(3/2)^(s-1)` is a strictly monotone geometric sequence -- the tie `s=5` is not
        a maximum, minimum, or resonance of it (no kernel/projection event at the tie)."""
        vals = [near_star_determinant_closed_form(s) for s in self.near_star_s]
        strictly_geometric = all(b == a * Fr(3, 2) for a, b in zip(vals, vals[1:]))
        return strictly_geometric

    def finding(self) -> str:
        return (
            "NEGATIVE for localization; the object is right-shaped but generic. The Girardeau object "
            "per(L)/prod(deg) = prod_{lambda>0}(1+lambda^2) = |det(I+iN)| is a genuine non-separable "
            "FUNCTIONAL DETERMINANT (free-fermion determinantal point process). But on near-stars the "
            "normalized adjacency has the rigid spectrum {0, +-1, +-1/sqrt2 (mult s-1)} -- the same eigenvalue "
            "SET for all s -- so the determinant is the clean geometric closed form 2*(3/2)^(s-1), in which "
            "the tie s=5 (81/8) is unremarkable: no eigenvalue crossing, no rank collapse, no projection "
            "resonance. The determinantal SHAPE is right (non-separable, integer-derived kernel) but it does "
            "not localize the tie, because the tie is the ARITHMETIC balance (64/621)^n (prod a)^11 = 1 of the "
            "(64/621)^n weight against this spectral growth -- and a determinant carries no such arithmetic. "
            "Only the 23-adic carrier localizes the tie. conjecture1_proved = False."
        )

    def check(self) -> bool:
        """Certifies: the Girardeau object is a determinant with a clean geometric closed form, the spectrum
        is generic across near-stars, and the determinant does not localize the tie -- NOT BG."""
        return (
            self.girardeau_matches_closed_form()
            and self.spectrum_generic_across_near_stars()
            and self.determinant_does_not_localize_tie()
        )
