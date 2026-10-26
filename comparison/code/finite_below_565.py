"""Finite range (lead): for EVERY fundamental discriminant D = -q with 3 <= q < 565, compute h(D) directly as the number of reduced
primitive positive-definite forms (a, b, c), b^2 - 4ac = D, |b| <= a <= c, b >= 0 if |b| = a or a = c. Independent of any sieve."""
import math
def squarefree(n): return all(n % (p * p) for p in range(2, int(math.isqrt(n)) + 1))
def fundamental(q):
    if q % 4 == 3: return squarefree(q)
    if q % 4 == 0: m = q // 4; return m % 4 in (1, 2) and squarefree(m)
    return False
def h(D):
    q = -D; cnt = 0; a = 1
    while 3 * a * a <= q:
        for b in range(-a + 1, a + 1):
            if (b * b - D) % (4 * a): continue
            c = (b * b - D) // (4 * a)
            if c < a or math.gcd(math.gcd(a, abs(b)), c) != 1: continue
            if b < 0 and (a == c): continue
            cnt += 1
        a += 1
    return cnt
fund = [q for q in range(3, 565) if fundamental(q)]
ones = [q for q in fund if h(-q) == 1]
print(f"fundamental discriminants with 3 <= q < 565: {len(fund)}; those with h = 1: {ones}")
assert ones == [3, 4, 7, 8, 11, 19, 43, 67, 163]
# cross-check the class number formula against known values
assert h(-23) == 3 and h(-47) == 5 and h(-71) == 7 and h(-15) == 2 and h(-20) == 2
print("exactly the nine Heegner discriminants: OK")
