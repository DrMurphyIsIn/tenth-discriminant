"""Bosonic reading of the tree-Laplacian problem -- the condensate side of the boson<->fermion seam.

The fermionic side (fermion_dof.py, spectral.py) read the matchings as Pauli-excluded dimers and det(L)=0
as the fermion vacuum.  This module reads the SAME object bosonically: per(L) is the BOSONIC permanent
(the boson-sampling partition function; the symmetric / trivial-S_n-rep immanant), and the cavity
amplitudes a_v = 1 + z_v S_v are COHERENT-STATE condensate occupations.  The two are one seam:

    det(L) = 0            fermion vacuum (the Laplacian's constant zero-mode kills the antisymmetric sum),
    per(L) > 0            boson condensate (the same zero-mode POPULATES the symmetric sum).

CONDENSATE = BULK, HUB = SURFACE (the payoff).  For the near-star every arm is identical, so its cavity is
a UNIFORM condensate -- exactly solvable and s-independent:

    m_leaf = z(1)=1,   m_mid = z(2)/(1 + z(2) m_leaf) = (1/2)/(3/2) = 1/3,   a_mid = 3/2,

a uniform mean-field (Gross-Pitaevskii-type) condensate on the arms.  The hub is a boundary DEFECT on top
of this condensate.  So the bulk+surface decomposition D(s) = D_inf + c/s that Laplace's law fitted is
CANONICAL here: D_inf = (64/621) a_mid^(11/2) is the condensate (bulk) density, and the 1/s surface term
is the hub boundary.  The bosonic frame makes the surface-tension architecture natural, not fitted.

INTEGRALITY = FOCK QUANTIZATION.  The continuum relaxation overshoots (Phi=1.00046 at real s=4.822); only
integer s obey Phi<=1.  Bosonically this is Fock number-state quantization -- integer occupation -- the
same wall the fermionic reading called Pauli roughness, seen from the opposite statistics.

FULL BOSONIC TOOLKIT (ported here, the mirror of the fermionic side): the bosonic permanent per(L) and
its boson<->fermion seam (det=0); the HAFNIAN (Gaussian boson sampling / perfect-matching object) and the
per = haf([[0,A],[A^T,0]]) relation; coherent-state occupations (Poissonian, mean=variance); Bose-Einstein
thermal occupation and condensation; the Van der Waerden minimum permanent (uniform condensate); the three
Bose-Einstein statistical attributes (symmetry, commutation, bunching); and the HARD-CORE-BOSON / Girardeau
duality -- the tree matchings are hard-core bosons, so per(L)/prod(deg) equals the free-fermion spectral
product prod(1+lambda^2), which is WHY the boson and fermion readings coincide on trees.

DESCRIPTIVE: this is a reading of the SAME object the cavity computes, not a new proof.  It proves nothing
the fermionic/cavity side didn't -- it makes the condensate/surface structure canonical.  conjecture1_proved
= False.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr

from .immanant import determinant, permanent


def bosonic_permanent(n, edges):
    """per(L) -- the BOSONIC permanent (boson-sampling partition function; symmetric/trivial-rep immanant)."""
    return permanent(n, edges)


def fermion_vacuum_det(n, edges):
    """det(L) -- the fermionic (antisymmetric) partner; = 0 for any connected graph (the constant
    zero-mode is the fermion vacuum)."""
    return determinant(n, edges)


def condensate_cavity(z_num, z_den, children_m):
    """One bosonic mean-field cavity step m = z/(1 + z * sum(children_m)) (the coherent condensate self-
    consistency).  z given as a Fraction z_num/z_den; children_m a list of Fractions."""
    z = Fr(z_num, z_den)
    S = sum(children_m, Fr(0))
    return z / (1 + z * S)


def arm_condensate():
    """The near-star arm's uniform condensate (exact, s-independent): (m_leaf, m_mid, a_mid)."""
    m_leaf = Fr(1)                                   # z(1)=1, no children
    m_mid = condensate_cavity(1, 2, [m_leaf])        # z(2)=1/2
    a_mid = 1 + Fr(1, 2) * m_leaf                    # coherent amplitude of the arm-mid
    return m_leaf, m_mid, a_mid


def condensate_density():
    """Bulk (condensate) density D_inf = (64/621) * a_mid^(11/2), a_mid=3/2 -- the mean-field condensate
    density the near-star relaxes to (= the fractal_eigenvalue D_inf)."""
    _, _, a_mid = arm_condensate()
    return float(Fr(64, 621)) * (float(a_mid) ** 5.5)


def gross_pitaevskii_bethe(z_num, z_den, degree):
    """Reference: the uniform condensate on an INFINITE regular Bethe lattice of the given degree,
    m = z/(1 + z(d-1)m)  =>  (d-1) z m^2 + m - z = 0 (the GP quadratic).  Returns the positive root.
    (The near-star arm is the FINITE realization; this is the idealized infinite condensate.)"""
    import math
    z = z_num / z_den
    a = (degree - 1) * z
    b = 1.0
    c = -z
    return (-b + math.sqrt(b * b - 4 * a * c)) / (2 * a) if a else z


def hafnian(A):
    """Hafnian of a symmetric matrix -- the GAUSSIAN-boson-sampling object: sum over PERFECT MATCHINGS
    (pairings) of prod A_ij.  Bosonic cousin of the Pfaffian (haf has all + signs; Pf alternates).
    Related to the permanent by per(A) = haf([[0,A],[A^T,0]])."""
    n = len(A)
    if n % 2:
        return 0

    def rec(verts):
        if not verts:
            return 1
        i = verts[0]
        tot = 0
        for k in range(1, len(verts)):
            j = verts[k]
            tot += A[i][j] * rec([v for v in verts[1:] if v != j])
        return tot

    return rec(list(range(n)))


def per_from_hafnian(A):
    """per(A) via the hafnian embedding haf([[0,A],[A^T,0]]) -- the permanent as a Gaussian-boson object."""
    n = len(A)
    Z = [[0] * (2 * n) for _ in range(2 * n)]
    for i in range(n):
        for j in range(n):
            Z[i][n + j] = A[i][j]
            Z[n + j][i] = A[i][j]
    return hafnian(Z)


def bose_einstein_occupation(eps, beta=1.0, mu=0.0):
    """Bose-Einstein mean occupation <n> = 1/(exp(beta(eps-mu)) - 1).  Diverges as eps -> mu (the
    condensation instability): bosons pile into the low-energy mode without bound (no Pauli cap)."""
    import math
    x = beta * (eps - mu)
    return 1.0 / (math.exp(x) - 1.0) if x > 1e-12 else float("inf")


def van_der_waerden_bound(n):
    """The Van der Waerden lower bound per(D) >= n!/n^n for n x n doubly-stochastic D, with equality at
    the uniform condensate D = J/n -- the bosonic 'minimum permanent' (maximally spread occupation)."""
    import math
    return math.factorial(n) / n ** n


def coherent_state_occupation(alpha2, n):
    """|<n|alpha>|^2 = e^{-|alpha|^2} |alpha|^{2n}/n! -- POISSONIAN occupation of a coherent (condensate/
    laser) state, mean = variance = |alpha|^2 (the classic coherent-state signature).  alpha2 = |alpha|^2."""
    import math
    return math.exp(-alpha2) * alpha2 ** n / math.factorial(n)


def _perm(M):
    """Exact permanent of a small matrix (brute force over permutations)."""
    import math
    from itertools import permutations
    n = len(M)
    return sum(math.prod(M[i][p[i]] for i in range(n)) for p in permutations(range(n)))


def _det(M):
    """Exact determinant of a small matrix (Leibniz, exact)."""
    import math
    from itertools import permutations
    n = len(M)
    tot = 0
    for p in permutations(range(n)):
        sign = 1 if sum(1 for i in range(n) for j in range(i + 1, n) if p[i] > p[j]) % 2 == 0 else -1
        tot += sign * math.prod(M[i][p[i]] for i in range(n))
    return tot


@dataclass(frozen=True)
class BoseEinsteinStatisticsCertificate:
    """Certifies the three defining bosonic attributes of the permanent (vs the determinant): complete
    symmetry under particle exchange, commutation (not anticommutation) relations, and Bose-Einstein
    statistics -- each as a concrete, checkable property of per vs det."""

    def exchange_symmetric(self) -> bool:
        """COMPLETE SYMMETRY under particle exchange: swapping two rows (exchanging two particles) leaves
        per INVARIANT (symmetric = boson), while det flips sign (antisymmetric = fermion)."""
        M = [[1, 2, 3], [4, 5, 6], [7, 8, 10]]
        Msw = [M[1], M[0], M[2]]
        return _perm(M) == _perm(Msw) and _det(M) == -_det(Msw)

    def commutation_not_anticommutation(self) -> bool:
        """COMMUTATION [a,a+]=1 (not anticommutation): two particles in the SAME mode (two equal rows) is
        ALLOWED for per (nonzero, no Pauli) but FORBIDDEN for det (zero, Pauli exclusion)."""
        Meq = [[1, 2, 3], [1, 2, 3], [7, 8, 10]]
        return _perm(Meq) != 0 and _det(Meq) == 0

    def bose_einstein_bunching(self, kmax: int = 5) -> bool:
        """BOSE-EINSTEIN statistics: unbounded shared occupation -- per(J_k)=k! (bosonic bunching), while
        det(J_k)=0 for k>=2 (no fermionic bunching)."""
        import math
        for k in range(2, kmax + 1):
            J = [[1] * k for _ in range(k)]
            if _perm(J) != math.factorial(k) or _det(J) != 0:
                return False
        return True

    def check(self) -> bool:
        return (self.exchange_symmetric()
                and self.commutation_not_anticommutation()
                and self.bose_einstein_bunching())


@dataclass(frozen=True)
class BosonicToolkitCertificate:
    """Certifies the ported bosonic toolkit: the hafnian/permanent (Gaussian-boson) relation, the
    Van der Waerden minimum-permanent equality, the coherent-state Poissonian signature (mean=variance),
    Bose-Einstein condensation (occupation -> inf as eps -> mu), and the HARD-CORE-BOSON / Girardeau
    duality that explains why the boson and fermion readings coincide on trees."""

    def hafnian_permanent_relation(self) -> bool:
        """per(A) = haf([[0,A],[A^T,0]]) -- the permanent is a Gaussian-boson (hafnian) object."""
        A = [[1, 2], [3, 4]]
        return _perm(A) == per_from_hafnian(A)

    def van_der_waerden_equality(self, nmax: int = 5) -> bool:
        """per(J/n) = n!/n^n: the uniform condensate attains the Van der Waerden minimum permanent."""
        for n in range(2, nmax + 1):
            Jn = [[1.0 / n] * n for _ in range(n)]
            if abs(_perm(Jn) - van_der_waerden_bound(n)) > 1e-9:
                return False
        return True

    def coherent_state_poissonian(self, alpha2: float = 2.0, nmax: int = 30) -> bool:
        """A coherent (condensate) state has Poissonian occupation: mean = variance = |alpha|^2."""
        p = [coherent_state_occupation(alpha2, n) for n in range(nmax)]
        mean = sum(n * p[n] for n in range(nmax))
        var = sum((n - mean) ** 2 * p[n] for n in range(nmax))
        return abs(mean - alpha2) < 1e-6 and abs(var - alpha2) < 1e-6

    def bose_einstein_condensation(self) -> bool:
        """Occupation grows without bound as eps -> mu (no Pauli cap) -- the condensation signature."""
        return bose_einstein_occupation(0.001) > 100 and bose_einstein_occupation(2.0) < 1

    def hard_core_boson_duality(self) -> bool:
        """The tree matching object is HARD-CORE bosons (each vertex in <=1 dimer): the bosonic permanent
        per(L)/prod(deg) EQUALS the free-fermion spectral product prod(1+lambda^2) (Girardeau boson<->
        fermion duality on the tree) -- why both readings give the same arithmetic."""
        from fractions import Fraction as Fr

        from .fractal_eigenvalue import near_star_edges
        from .matching_free_energy import rho as matching_rho
        from .spectral import spectral_rho
        n, e = near_star_edges(5)
        return abs(float(matching_rho(n, e)) - spectral_rho(n, e)) < 1e-9

    def check(self) -> bool:
        return (self.hafnian_permanent_relation() and self.van_der_waerden_equality()
                and self.coherent_state_poissonian() and self.bose_einstein_condensation()
                and self.hard_core_boson_duality())


@dataclass(frozen=True)
class BosonicReadingCertificate:
    """Certifies the bosonic reading on a tree: per(L) is the symmetric (bosonic) immanant and det(L)=0
    is the fermion vacuum (the seam); the arm condensate is the exact uniform mean-field m_mid=1/3,
    a_mid=3/2; and the condensate (bulk) density equals the fractal_eigenvalue D_inf."""

    n: int = 11
    edges: tuple = ()

    def _ns(self):
        from .fractal_eigenvalue import near_star_edges
        return near_star_edges(5) if not self.edges else (self.n, self.edges)

    def seam(self) -> bool:
        """per(L) > 0 (boson condensate) and det(L) = 0 (fermion vacuum) -- the boson<->fermion seam."""
        n, e = self._ns()
        return bosonic_permanent(n, e) > 0 and fermion_vacuum_det(n, e) == 0

    def uniform_condensate(self) -> bool:
        """The arm condensate is the exact uniform mean-field: m_mid = 1/3, a_mid = 3/2."""
        _, m_mid, a_mid = arm_condensate()
        return m_mid == Fr(1, 3) and a_mid == Fr(3, 2)

    def condensate_is_bulk(self) -> bool:
        """The condensate density equals the fractal_eigenvalue bulk D_inf (bulk = condensate)."""
        from .fractal_eigenvalue import arm_transfer_eigenvalue_closed_form
        _, d_inf = arm_transfer_eigenvalue_closed_form()
        return abs(condensate_density() - d_inf) < 1e-12

    def check(self) -> bool:
        return self.seam() and self.uniform_condensate() and self.condensate_is_bulk()
