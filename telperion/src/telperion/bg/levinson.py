"""Levinson's theorem for tree impurities -- bound-state count from the scattering phase shift.

A rank-1 on-site impurity V|r><r| on a Hermitian host H0 has secular function
    f(E) = 1 - V * G0_rr(E),   G0_rr(E) = sum_k |<k|r>|^2 / (E - lambda_k),
whose zeros OUTSIDE the host band are exactly the impurity bound states (rank-1 / Weinstein-Aronszajn).
Levinson's theorem: the number of bound states equals the winding of the phase delta(E) = arg f(E+i0)
across the band -- pi per bound state.

FLAT BAND (the near-star).  With H0 = adjacency A, the near-star N(0,s) has degenerate modes at +-1 of
multiplicity s-1 whose weight at the hub is ZERO: DARK STATES, decoupled from the impurity.  They carry
no phase shift (delta = 0) and are excluded from the Levinson count -- the hub impurity creates exactly
ONE bright bound state regardless of s.  The arm-permutation symmetry protects the flat band; the tie
resonance lives in the bright channel (Friedel response R = (4s+3)/(4(s+1)) = 23/24 at s=5).

This module verifies Levinson's counting for tree impurities and exposes the dark/bright split.
"""
from __future__ import annotations

from dataclasses import dataclass

try:
    import numpy as np
    import networkx as nx
    _OK = True
except Exception:  # pragma: no cover
    _OK = False


@dataclass
class LevinsonAnalysis:
    """Rank-1 on-site impurity V at `site` on a Hermitian host H0 (numpy array)."""

    H0: object
    site: int
    V: float
    tol: float = 1e-7

    def _spec(self):
        return np.linalg.eigh(self.H0)

    def host_band(self):
        lam, _ = self._spec()
        return float(lam.min()), float(lam.max())

    def spectral_weights(self):
        """|<k|site>|^2 for each host mode k (coupling of the impurity to each mode)."""
        lam, U = self._spec()
        return lam, np.abs(U[self.site, :]) ** 2

    def dark_modes(self):
        """The FLAT BAND: (energy, multiplicity) of modes with ~zero weight at the impurity site."""
        lam, w = self.spectral_weights()
        from collections import Counter
        return dict(Counter(round(float(lam[k]), 4) for k in range(len(lam)) if w[k] < self.tol))

    def perturbed_spectrum(self):
        H = np.array(self.H0, dtype=float).copy()
        H[self.site, self.site] += self.V
        return np.linalg.eigvalsh(H)

    def bound_states(self):
        """Eigenvalues of H0 + V e_site e_site^T lying OUTSIDE the host band."""
        lo, hi = self.host_band()
        full = self.perturbed_spectrum()
        above = [float(x) for x in full if x > hi + self.tol]
        below = [float(x) for x in full if x < lo - self.tol]
        return below, above

    def secular(self, E):
        lam, w = self.spectral_weights()
        return 1 - self.V * np.sum(w / (E - lam))

    def levinson_count(self):
        """Bound-state count predicted by the secular function outside the band (= phase winding)."""
        lo, hi = self.host_band()
        lam, w = self.spectral_weights()
        # above the band f increases 1-V*G0(hi+) -> 1; one zero iff V*G0(hi+)>1 (V>0). scan for robustness.
        def count(direction):
            edge = hi if direction > 0 else lo
            Es = edge + direction * np.concatenate([np.linspace(1e-6, 5, 4000),
                                                    np.linspace(5, 5000, 2000)])
            vals = np.array([self.secular(E) for E in Es])
            return int(np.sum(np.abs(np.diff(np.sign(vals))) > 0))
        return count(-1), count(+1)

    def verify(self) -> bool:
        """Levinson: secular-function bound-state count == actual eigenvalue count outside the band."""
        below, above = self.bound_states()
        lc_below, lc_above = self.levinson_count()
        return lc_below == len(below) and lc_above == len(above)

    # ---- Friedel sum rule / Krein spectral shift ---------------------------
    # The DISPLACED CHARGE xi(E) = N_{H0}(E) - N_H(E) equals the phase over pi:
    #     xi(E) = (1/pi) arg(1 - V G0_rr(E+i0))            (Birman-Krein / Friedel sum rule),
    # and xi at the band edge = the bound-state count (Levinson is its boundary value).
    #
    # HONEST FINDING: the displaced charge does NOT discriminate the near-star.  A positive on-site
    # impurity creates exactly ONE bound state on EVERY tree, so xi is tree-independent.  BG's
    # extremality lives in the AMPLITUDE R = |1+G_rr| deg/(deg+1) (the arithmetic 23/24 resonance),
    # NOT in the phase / displaced charge.  So the counting/topological (Levinson-Friedel) invariants do
    # not by themselves prove extremality -- the amplitude does.

    def spectral_shift_count(self, E):
        """xi(E) = N_{H0}(E) - N_H(E) (difference of eigenvalue counting functions)."""
        lam0, _ = self._spec()
        lam1 = self.perturbed_spectrum()
        return int(np.sum(lam0 <= E) - np.sum(lam1 <= E))

    def spectral_shift_phase(self, E, eps=1e-6):
        """xi(E) via the Friedel phase: (1/pi) arg(1 - V G0_rr(E+i eps))."""
        import cmath
        lam, w = self.spectral_weights()
        G0 = np.sum(w / (E + 1j * eps - lam))
        return cmath.phase(1 - self.V * G0) / np.pi

    def displaced_charge(self, E):
        """The Friedel displaced charge at Fermi level E (= spectral shift xi(E))."""
        return self.spectral_shift_count(E)

    def verify_friedel_sum_rule(self, grid=None) -> bool:
        """The Friedel sum rule: xi_count(E) == round(xi_phase(E)) across an energy grid."""
        lo, hi = self.host_band()
        if grid is None:
            grid = np.linspace(lo - 2, hi + 2, 40)
        return all(self.spectral_shift_count(E) == round(self.spectral_shift_phase(E))
                   for E in grid)


def tree_levinson(n, edges, site, V):
    """LevinsonAnalysis for the tree adjacency host with an on-site impurity V at `site`."""
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(edges)
    A = nx.to_numpy_array(G, nodelist=range(n))
    return LevinsonAnalysis(A, site, V)
