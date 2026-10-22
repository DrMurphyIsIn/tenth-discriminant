#!/usr/bin/env python3
"""Generate the two radicand sets of the HCN statement from the COMPUTED class-number data, and write the statement file.

The sets are never typed by hand. This script:
  1. enumerates the fundamental discriminants -d, 3 <= d <= DMAX, from the definition (independent of the data files);
  2. reads h(-d) from the data in data/ (next to this script):
       - PARI qfbclassno          (classno_300000_gp.csv.gz,               d <= 300,000; data/gp_classno.gp)
       - reduced-form count, C    (classno_300000_forms_dirichlet.csv.gz h_forms; classno_340000_forms.csv.gz;
                                   data/hcn_classno.c)
       - Dirichlet's class number formula, C (classno_300000_forms_dirichlet.csv.gz h_dirichlet)
     plus an independent reduced-form count (classno_340000_independent.csv; data/independent_classno.c), and a fifth,
     in-script reduced-form count for d <= 5000;
  3. checks that every key set equals the enumerated fundamental set on its range and that all methods agree on every key;
  4. converts each d with h <= 2 to its radicand m (d = m if m = 3 mod 4, else d = 4m; CN-1's dOf), and checks
     squarefree m and dOf m = d;
  5. writes <out>/HCNChallenges/ClassNumberLeTwo.lean from the template below, with the sets inserted, and the h >= 3
     radicand list with dOf m <= 4777 (which gen_certs.py must reproduce) to <out>/radicands_ge3_4777.txt.

Usage: python3 gen_sets.py <out>   (about 10 s; regenerate_and_diff.sh runs it)
"""
import csv, gzip, math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
INDEPENDENT = os.path.join(DATA, "classno_340000_independent.csv")
OUTDIR = sys.argv[1] if len(sys.argv) > 1 else "."
OUT_LEAN = os.path.join(OUTDIR, "HCNChallenges", "ClassNumberLeTwo.lean")
OUT_RAD = os.path.join(OUTDIR, "radicands_ge3_4777.txt")
DMAX = 340000
DFIN = 4777  # the finite range of the proof


def squarefree(n):
    if n < 1:
        return False
    k = 2
    while k * k <= n:
        if n % (k * k) == 0:
            return False
        k += 1
    return True


def fundamental(d):
    """-d is a fundamental discriminant (d >= 3)."""
    if d % 4 == 3:
        return squarefree(d)
    if d % 4 == 0:
        m = d // 4
        return m % 4 in (1, 2) and squarefree(m)
    return False


def dOf(m):
    return m if m % 4 == 3 else 4 * m


def radicand(d):
    return d if d % 4 == 3 else d // 4


def h_reduced(d):
    """Number of reduced primitive positive definite forms of discriminant -d: |b| <= a <= c, b >= 0 if |b| = a or a = c."""
    D = -d
    h = 0
    a = 1
    while 3 * a * a <= d:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a):
                continue
            c = (b * b - D) // (4 * a)
            if c < a:
                continue
            if b < 0 and a == c:
                continue
            if math.gcd(math.gcd(a, abs(b)), c) != 1:
                continue
            h += 1
        a += 1
    return h


def read_csv(path, gz, cols):
    op = gzip.open if gz else open
    out = {}
    with op(path, "rt") as f:
        rows = list(csv.reader(f))
    start = 1 if not rows[0][0].isdigit() else 0
    for r in rows[start:]:
        out[int(r[0])] = tuple(int(r[c]) for c in cols)
    return out


def main():
    fund = [d for d in range(3, DMAX + 1) if fundamental(d)]
    fund300 = [d for d in fund if d <= 300000]
    gp = {d: v[0] for d, v in read_csv(f"{DATA}/classno_300000_gp.csv.gz", True, [1]).items()}
    fd = read_csv(f"{DATA}/classno_300000_forms_dirichlet.csv.gz", True, [1, 2])
    f340 = {d: v[0] for d, v in read_csv(f"{DATA}/classno_340000_forms.csv.gz", True, [1]).items()}
    ind = {d: v[0] for d, v in read_csv(INDEPENDENT, False, [1]).items()}
    assert sorted(gp) == fund300, "PARI key set != fundamental d <= 300000"
    assert sorted(fd) == fund300, "forms/Dirichlet key set != fundamental d <= 300000"
    assert sorted(f340) == fund, "forms-340000 key set != fundamental d <= 340000"
    assert sorted(ind) == fund, "independent key set != fundamental d <= 340000"
    for d in fund300:
        assert gp[d] == fd[d][0] == fd[d][1] == f340[d] == ind[d], f"mismatch at d={d}"
    for d in fund:
        assert f340[d] == ind[d], f"mismatch (300000, 340000] at d={d}"
    for d in fund:
        if d <= 5000:
            assert h_reduced(d) == f340[d], f"in-script count mismatch at d={d}"
    n_fin = sum(1 for d in fund if d <= DFIN)
    h1 = sorted(radicand(d) for d in fund if f340[d] == 1)
    h2 = sorted(radicand(d) for d in fund if f340[d] == 2)
    for m in h1 + h2:
        assert squarefree(m) and fundamental(dOf(m))
    for d in fund:
        assert dOf(radicand(d)) == d
    assert max(dOf(m) for m in h1 + h2) <= DFIN
    ge3 = sorted(radicand(d) for d in fund if d <= DFIN and f340[d] >= 3)
    s27 = h1 + h2
    print(f"fundamental d <= {DMAX}: {len(fund)}; <= 300000: {len(fund300)}; <= {DFIN}: {n_fin}")
    print("all five sources agree on every key (PARI, forms C, Dirichlet C, forms-340000 C, independent count); "
          "in-script count to 5000")
    print(f"h = 1 radicands ({len(h1)}): {h1}")
    print(f"h = 2 radicands ({len(h2)}): {h2}")
    print(f"h >= 3 with dOf m <= {DFIN}: {len(ge3)} radicands (largest {max(ge3)})")
    assert len(h1) == 9 and len(h2) == 18 and n_fin == 1456 and len(ge3) == 1429
    os.makedirs(os.path.dirname(OUT_LEAN), exist_ok=True)
    with open(OUT_RAD, "w") as f:
        f.write("\n".join(map(str, ge3)) + "\n")
    lit = lambda xs: ", ".join(map(str, xs))
    with open(OUT_LEAN, "w") as f:
        f.write(TEMPLATE.replace("@S27@", lit(s27)).replace("@S18@", lit(h2)))
    print(f"wrote {OUT_LEAN}")
    print(f"wrote {OUT_RAD}")


TEMPLATE = r'''import Mathlib

/-!
# HCN Comparator challenge: the imaginary quadratic fields of class number at most two

Statements only (`sorry`); the proofs are the solution side. GENERATED by hcn/certificates/gen_sets.py from the
COMPUTED class-number data (hcn/certificates/data; PARI, reduced forms and Dirichlet's formula agree, and so does an
independent count); the two radicand sets below are inserted by that script and are never typed by hand.
The import closure is Mathlib alone (Lean v4.34.1, Mathlib d13f23b, the openai/math 7/8 environment). Trust base:
these statements, the Mathlib definitions they use (`NumberField`, `NumberField.classNumber`, `Module.finrank`,
`Squarefree`), the Lean kernel and nanoda, and the axioms `propext`, `Classical.choice`, `Quot.sound`.

Template: `CN1.classNumber_eq_one_iff` (CN1Challenges/ClassNumberOne.lean). The same conventions: `m` is the
radicand, not the discriminant (`|disc ℚ(√-m)| = m` if `m ≡ 3 (mod 4)` and `4m` otherwise); `Squarefree m` forces
`m ≠ 0`, so `α` is irrational and `K ≅ ℚ(√-m)`. The first nine elements of the 27-element set are CN-1's set.
-/

open NumberField

namespace HCN

/-- **Class number at most two for imaginary quadratic fields.** Let `K` be a number field of degree two over `ℚ`
containing a square root of `-m`, where `m` is a squarefree natural number (so `m ≥ 1` and `K ≅ ℚ(√-m)`). Then the
class number of `K` is at most two if and only if `m` is one of the 27 radicands below (9 with class number one,
then 18 with class number two). -/
theorem classNumber_le_two_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K ≤ 2 ↔ m ∈ ({@S27@} : Finset ℕ) := by
  sorry

/-- **Class number two for imaginary quadratic fields.** Under the same hypotheses, the class number of `K` is
exactly two if and only if `m` is one of the 18 radicands below. -/
theorem classNumber_eq_two_iff (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2)
    (m : ℕ) (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) :
    classNumber K = 2 ↔ m ∈ ({@S18@} : Finset ℕ) := by
  sorry

end HCN
'''

if __name__ == "__main__":
    main()
