#!/usr/bin/env python3
"""
Split-prime witnesses for the finite part of the class number one theorem.

For every fundamental discriminant D = -d with 4 < d <= DMAX (= 652):
  * decide whether some prime p < (d+1)/4 splits in K = Q(sqrt(-d)), i.e. Kronecker (D/p) = 1,
    and record the least such p as the witness (or None);
  * record the radicand m (K = Q(sqrt(-m)), m squarefree) and the case: d = m with d = 3 mod 4
    (principal form b = 1) or d = 4m (principal form b = 0);
  * compute h(-d) independently in two ways: by counting reduced primitive binary quadratic forms
    of discriminant -d, and by Dirichlet's class number formula h = -(1/d) sum_{a<d} a * chi(a)
    (valid for d > 4, where w = 2);
  * cross-check: witness exists  <=>  h(-d) > 1  (this is the Rabinowitsch-style equivalence;
    only the direction "witness => h != 1" is needed by the Lean proof, CN1.Finite).

Everything here is COMPUTED: it is evidence and generator input, not part of the Lean proof.
Pure Python; sympy is used only for a second opinion on primality and the Legendre symbol.

Output: witnesses.json next to this file (or the path given as the first argument).
"""
import json
import math
import os
import sys

DMAX = 652
HEEGNER_D = {3, 4, 7, 8, 11, 19, 43, 67, 163}  # |disc| of the nine Heegner fields
HEEGNER_M = {1, 2, 3, 7, 11, 19, 43, 67, 163}  # the radicands


# ---------------------------------------------------------------- elementary number theory

def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def primes_below(n):
    """Primes p with p < n (strict)."""
    return [p for p in range(2, n) if is_prime(p)]


def is_squarefree(n):
    if n <= 0:
        return False
    i = 2
    while i * i <= n:
        if n % (i * i) == 0:
            return False
        i += 1
    return True


def legendre(a, p):
    """Legendre symbol (a/p) for an odd prime p, via Euler's criterion."""
    a %= p
    if a == 0:
        return 0
    r = pow(a, (p - 1) // 2, p)
    return 1 if r == 1 else -1


def legendre_bruteforce(a, p):
    """Independent check of legendre(): is a a nonzero square mod p?"""
    a %= p
    if a == 0:
        return 0
    return 1 if any((x * x) % p == a for x in range(1, p)) else -1


def kronecker_prime(D, p):
    """Kronecker symbol (D/p) for a prime p and any integer D."""
    if p == 2:
        if D % 2 == 0:
            return 0
        return 1 if D % 8 in (1, 7) else -1
    return legendre(D, p)


def kronecker(D, n):
    """Kronecker symbol (D/n) for n >= 1, multiplicative over the prime factorisation of n."""
    if n == 1:
        return 1
    result = 1
    m = n
    p = 2
    while p * p <= m:
        while m % p == 0:
            result *= kronecker_prime(D, p)
            if result == 0:
                return 0
            m //= p
        p += 1
    if m > 1:
        result *= kronecker_prime(D, m)
    return result


# ---------------------------------------------------------------- fundamental discriminants

def fundamental_negative(d):
    """
    Is D = -d a fundamental discriminant?  Returns (is_fundamental, m, case) where
      case 'b1': d = 3 mod 4, d squarefree, m = d            (D = 1 mod 4, principal form x^2 + xy + (d+1)/4 y^2)
      case 'b0': d = 4m, m squarefree, m = 1 or 2 mod 4       (D = 4 * (-m), -m = 2 or 3 mod 4, principal form x^2 + m y^2)
    """
    if d % 4 == 3 and is_squarefree(d):
        return True, d, "b1"
    if d % 4 == 0:
        m = d // 4
        if is_squarefree(m) and m % 4 in (1, 2):
            return True, m, "b0"
    return False, None, None


# ---------------------------------------------------------------- class numbers, two ways

def class_number_reduced_forms(d):
    """
    h(-d) = number of primitive reduced forms (a, b, c), b^2 - 4ac = -d, with
      |b| <= a <= c, and b >= 0 if |b| = a or a = c.
    """
    D = -d
    count = 0
    forms = []
    a_max = int(math.isqrt(d // 3)) + 1
    for a in range(1, a_max + 1):
        for b in range(-a, a + 1):
            num = b * b - D  # = b^2 + d = 4ac
            if num % (4 * a) != 0:
                continue
            c = num // (4 * a)
            if c < a:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            if math.gcd(math.gcd(a, abs(b)), c) != 1:
                continue
            count += 1
            forms.append((a, b, c))
    return count, forms


def class_number_dirichlet(d):
    """
    Dirichlet's class number formula for D = -d < -4 (w = 2):
      h(D) = -(1/|D|) * sum_{a=1}^{|D|-1} a * chi_D(a).
    """
    assert d > 4
    s = sum(a * kronecker(-d, a) for a in range(1, d))
    assert s % d == 0, (d, s)
    return -s // d


# ---------------------------------------------------------------- the witness search

def witness(d):
    """
    Least prime p with p < (d+1)/4 (i.e. 4p <= d) and (−d/p) = 1, or None.
    Also return the ramified primes in the same range (robustness note).
    """
    D = -d
    # p < (d+1)/4  <=>  4p < d+1  <=>  4p <= d  (integers)
    bound_excl = d // 4 + 1  # primes p with p <= d//4, i.e. p < bound_excl
    split = []
    ramified = []
    for p in primes_below(bound_excl):
        k = kronecker_prime(D, p)
        if k == 1:
            split.append(p)
        elif k == 0:
            ramified.append(p)
    return (split[0] if split else None), split, ramified, bound_excl - 1


def main():
    out_dir = os.path.dirname(os.path.abspath(__file__))
    rows = []
    n_fund = 0
    n_with = 0
    n_without = 0
    n_b1 = n_b0 = 0
    mismatches = []
    kron_checks = 0

    # Optional sympy second opinion on primality and Legendre symbols.
    try:
        import sympy
        have_sympy = True
    except Exception:
        have_sympy = False

    for d in range(5, DMAX + 1):
        fund, m, case = fundamental_negative(d)
        if not fund:
            continue
        n_fund += 1
        if case == "b1":
            n_b1 += 1
        else:
            n_b0 += 1

        w, split, ramified, pmax = witness(d)
        h_forms, forms = class_number_reduced_forms(d)
        h_dir = class_number_dirichlet(d)
        if h_forms != h_dir:
            mismatches.append(("h_forms != h_dirichlet", d, h_forms, h_dir))
        has_witness = w is not None
        if has_witness:
            n_with += 1
        else:
            n_without += 1
        if has_witness == (h_forms == 1):
            mismatches.append(("witness-existence vs h==1", d, w, h_forms))
        if (h_forms == 1) != (d in HEEGNER_D):
            mismatches.append(("h==1 vs Heegner list", d, h_forms))
        if (m in HEEGNER_M) != (d in HEEGNER_D):
            mismatches.append(("radicand/disc Heegner map", d, m))

        # Per-case representation bound: y != 0 gives Q >= (d+1)/4 (b=1) or Q >= d/4 (b=0).
        if case == "b1":
            min_nonaxial = (d + 1) // 4
            principal_form = (1, 1, (d + 1) // 4)
        else:
            min_nonaxial = d // 4
            principal_form = (1, 0, m)
        assert principal_form in forms, (d, principal_form, forms)

        # Independent checks of the Kronecker symbol on every prime in range.
        for p in primes_below(pmax + 1):
            if p != 2:
                assert legendre(-d, p) == legendre_bruteforce(-d, p), (d, p)
                if have_sympy:
                    expected = int(sympy.legendre_symbol((-d) % p, p)) if (-d) % p else 0
                    assert legendre(-d, p) == expected, (d, p)
                kron_checks += 1
            if have_sympy:
                assert sympy.isprime(p)

        rows.append({
            "d": d,
            "disc": -d,
            "m": m,
            "case": "d = 3 mod 4 (d = m, b = 1)" if case == "b1" else "d = 4m (b = 0)",
            "d_mod_4": d % 4,
            "principal_form": list(principal_form),
            "min_Q_y_nonzero": min_nonaxial,
            "witness_bound_strict": f"p < (d+1)/4 = {(d + 1) / 4}",
            "largest_admissible_p": pmax,
            "witness": w,
            "all_split_primes_below_bound": split,
            "ramified_primes_below_bound": ramified,
            "h_reduced_forms": h_forms,
            "h_dirichlet": h_dir,
            "reduced_forms": [list(f) for f in forms],
            "heegner": d in HEEGNER_D,
        })

    summary = {
        "range": f"fundamental discriminants -d with 4 < d <= {DMAX}",
        "n_fundamental": n_fund,
        "n_case_b1_d_eq_3_mod_4": n_b1,
        "n_case_b0_d_eq_4m": n_b0,
        "n_with_witness": n_with,
        "n_without_witness": n_without,
        "without_witness_d": [r["d"] for r in rows if r["witness"] is None],
        "without_witness_m": [r["m"] for r in rows if r["witness"] is None],
        "largest_fundamental_d_in_range": max(r["d"] for r in rows),
        "max_witness": max(r["witness"] for r in rows if r["witness"] is not None),
        "witness_histogram": {},
        "n_with_ramified_prime_below_bound": sum(1 for r in rows if r["ramified_primes_below_bound"]),
        "n_without_witness_but_ramified_below_bound": sum(
            1 for r in rows if r["witness"] is None and r["ramified_primes_below_bound"]),
        "class_number_cross_check": "reduced forms == Dirichlet formula for every d" if not any(
            x[0].startswith("h_forms") for x in mismatches) else "MISMATCH",
        "rabinowitsch_cross_check": "witness exists <=> h(-d) > 1 for every d" if not any(
            x[0].startswith("witness-existence") for x in mismatches) else "MISMATCH",
        "kronecker_checks_vs_bruteforce": kron_checks,
        "sympy_second_opinion": have_sympy,
        "mismatches": mismatches,
        "label": "COMPUTED (witnesses.py, 2026-10-21)",
    }
    hist = {}
    for r in rows:
        if r["witness"] is not None:
            hist[r["witness"]] = hist.get(r["witness"], 0) + 1
    summary["witness_histogram"] = {str(k): hist[k] for k in sorted(hist)}

    out_path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(out_dir, "witnesses.json")
    with open(out_path, "w") as f:
        json.dump({"summary": summary, "rows": rows}, f, indent=1)

    print(json.dumps(summary, indent=1))
    return 0 if not mismatches else 1


if __name__ == "__main__":
    sys.exit(main())
