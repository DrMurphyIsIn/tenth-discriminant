#!/usr/bin/env python3
"""Emit the bridge-free `classNumber K >= 3` certificates of the finite range as Lean.

Output: <out>/HCN/Finite/Certs/Chunk<k>.lean and <out>/HCN/Finite/Certs.lean (the aggregate). Do not edit the outputs
by hand.

Inputs (all COMPUTED, in data/ next to this script):
  * class numbers: classno_340000_forms.csv.gz (the reduced-form count, column h_forms), cross-checked against
    the independent count classno_340000_independent.csv and against a third reduced-form count done here, for every
    fundamental d <= DMAX;
  * for comparison only: cert_norm_4777.csv (the per-d chosen primes of an earlier, separate implementation). The
    certificates are RE-DERIVED here, never copied, and must agree with that file exactly;
  * gen_sets.py's radicand list <out>/radicands_ge3_4777.txt (must agree exactly).

The certificate: walk the primes 2, 3, 5, ... and record ONLY the chosen ones.
  (a) split: p prime, p does not divide d, and a root r of X^2 - t X + c mod p (the least r in [0, p) is emitted);
  (b) NotRep(p)                          -- if Q represents p:  SKIP p;
  (x) NotRep(p q) for each chosen q      -- if Q represents p q: SKIP p;
  (c) NotRepYNonzero(p^2)                 -- inverse flag f = (c) holds: 2 classes if f, 1 if not.
  Stop as soon as 1 + sum(2 if f else 1) >= 3. So a certificate never certifies more than the claim h >= 3.
Every hypothesis emitted is checked TRUE here, by the z-search and again by a brute-force (x, y) box search, before it
is written. The Lean kernel then re-decides each one.

Lean shape, per radicand m (t = tOf m, c = cOf m, d = dOf m), with every hypothesis visible and individually decided:
  theorem cert_m : ClassCert t c [(p1, r1, f1), ...] :=
    .cons (by decide +kernel : SplitW t c p1 r1 = true) (by decide +kernel : NotRep t c p1)
      (.cons (by decide +kernel : NotRep t c (p1 * p2)) (.nil ..)) (fun _ => by decide +kernel : NotRepYNonzero ...)
      (...)

Usage: python3 gen_certs.py <out> [--chunk N]
       python3 gen_certs.py --force-controls OUTDIR
  --force-controls writes the negative-control files (claim side d = 8, 15; witness side d = 23) to OUTDIR through
  the forcing adapter `emit_forced` below, which bypasses the honest generator's refusals. Those files are never
  written under the Lean library, and each must FAIL to build.
"""
import csv, gzip, os, sys
from math import isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
INDEPENDENT = os.path.join(DATA, "classno_340000_independent.csv")
OUTDIR = sys.argv[1] if len(sys.argv) > 1 and not sys.argv[1].startswith("--") else "."
RADLIST = os.path.join(OUTDIR, "radicands_ge3_4777.txt")
OUT = os.path.join(OUTDIR, "HCN", "Finite")
DMAX = 4777
TARGET = 2          # claim h >= TARGET + 1 = 3
EXPECT = dict(certs=1429, hyps=2895, witnesses=1466, pmax=71)


# ---------------------------------------------------------------- arithmetic

def is_prime(n):
    if n < 2:
        return False
    k = 2
    while k * k <= n:
        if n % k == 0:
            return False
        k += 1
    return True


PRIMES = [p for p in range(2, 5000) if is_prime(p)]


def squarefree(n):
    k = 2
    while k * k <= n:
        if n % (k * k) == 0:
            return False
        k += 1
    return True


def tcd(m):
    """CN-1's tOf, cOf, dOf (Finite/Params.lean)."""
    if m % 4 == 3:
        return 1, (m + 1) // 4, m
    return 0, m, 4 * m


def rep_z(t, c, n, y0=0):
    """The Lean search: some y >= y0, z >= 0 with z^2 + d y^2 = 4n and z = t y (mod 2)."""
    d = 4 * c - t * t
    y = y0
    while d * y * y <= 4 * n:
        s = 4 * n - d * y * y
        z = isqrt(s)
        if z * z == s and z % 2 == (t * y) % 2:
            return True
        y += 1
    return False


def rep_box(t, c, n, y_nonzero=False):
    """Independent check: brute force over the box |y| <= sqrt(4n/d), |x| <= sqrt(n) + |t y|."""
    d = 4 * c - t * t
    Y = isqrt(4 * n // d) + 1
    X = isqrt(n) + Y + 2
    for y in range(-Y, Y + 1):
        if y_nonzero and y == 0:
            continue
        for x in range(-X, X + 1):
            if x * x + t * x * y + c * y * y == n:
                return True
    return False


def notrep(t, c, n):
    a, b = not rep_z(t, c, n), not rep_box(t, c, n)
    assert a == b, ("NotRep methods disagree", t, c, n)
    return a


def notrep_y(t, c, n):
    a, b = not rep_z(t, c, n, 1), not rep_box(t, c, n, True)
    assert a == b, ("NotRepYNonzero methods disagree", t, c, n)
    return a


def root(t, c, p):
    rs = [r for r in range(p) if (r * r + c - t * r) % p == 0]
    return rs[0] if rs else None


def split_ok(t, c, p, r):
    """Mirror of the Lean `SplitW`."""
    d = 4 * c - t * t
    return is_prime(p) and d % p != 0 and t * r <= r * r + c and (r * r + c - t * r) % p == 0


def certificate(m):
    """The honest greedy. Returns the chosen list [(p, r, f)] or None if h >= 3 cannot be certified."""
    t, c, d = tcd(m)
    chosen, count = [], 1
    for p in PRIMES:
        if count >= TARGET + 1:
            break
        if d % p == 0:
            continue
        r = root(t, c, p)
        if r is None:
            continue
        if not notrep(t, c, p):
            continue                                   # P principal: skip
        if any(not notrep(t, c, p * q) for q, _, _ in chosen):
            continue                                   # its pair meets a chosen pair: skip
        f = notrep_y(t, c, p * p)
        chosen.append((p, r, f))
        count += 2 if f else 1
    return chosen if count >= TARGET + 1 else None


def weight(ch):
    return sum(2 if f else 1 for _, _, f in ch)


def hyps_of(ch):
    """The hypotheses of a certificate, in Lean order: (kind, n)."""
    out = []
    for i, (p, r, f) in enumerate(ch):
        out.append(("SplitW", (p, r)))
        out.append(("NotRep", p))
        for q, _, _ in ch[i + 1:]:
            out.append(("NotRep", p * q))
        if f:
            out.append(("NotRepYNonzero", p * p))
    return out


def check_true(t, c, ch):
    for kind, v in hyps_of(ch):
        if kind == "SplitW":
            assert split_ok(t, c, *v), (t, c, v)
        elif kind == "NotRep":
            assert notrep(t, c, v), (t, c, v)
        else:
            assert notrep_y(t, c, v), (t, c, v)


# ---------------------------------------------------------------- class numbers (three sources)

def h_reduced(d):
    """Count reduced primitive forms of discriminant -d (|b| <= a <= c, b >= 0 if |b| = a or a = c)."""
    from math import gcd
    n = 0
    a = 1
    while 3 * a * a <= d:
        for b in range(-a + 1, a + 1):
            if (b * b + d) % (4 * a):
                continue
            c = (b * b + d) // (4 * a)
            if c < a or (c == a and b < 0):
                continue
            if gcd(gcd(a, abs(b)), c) != 1:
                continue
            n += 1
        a += 1
    return n


def load_h():
    H = {}
    with gzip.open(f"{DATA}/classno_340000_forms.csv.gz", "rt") as f:
        r = csv.reader(f)
        next(r)
        for row in r:
            d = int(row[0])
            if d <= DMAX:
                H[d] = int(row[1])
    ind = {}
    for row in csv.reader(open(INDEPENDENT)):
        if row and row[0].isdigit() and int(row[0]) <= DMAX:
            ind[int(row[0])] = int(row[1])
    assert set(H) == set(ind) and all(H[d] == ind[d] for d in H), "forms count vs independent count disagree"
    for d in H:
        assert h_reduced(d) == H[d], ("in-script count disagrees", d)
    return H


# ---------------------------------------------------------------- Lean emission

def lean_bool(f):
    return "true" if f else "false"


def lean_list(ch):
    return "[" + ", ".join(f"({p}, {r}, {lean_bool(f)})" for p, r, f in ch) + "]"


def lean_cert_term(t, c, ch, override=None):
    """The `.cons` term. `override` (forcing adapter only) maps a hypothesis key to a replacement type string."""
    override = override or {}
    if not ch:
        return f"(.nil {t} {c})"
    (p, r, f), rest = ch[0], ch[1:]
    ha = override.get(("SplitW", p), f"SplitW {t} {c} {p} {r} = true")
    hb = override.get(("NotRep", p), f"NotRep {t} {c} {p}")
    pairs = f"(.nil {t} {c} {p})"
    for q, _, _ in reversed(rest):
        pairs = f"(.cons (by decide +kernel : NotRep {t} {c} ({p} * {q})) {pairs})"
    hc = (f"(fun _ => (by decide +kernel : {override.get(('NotRepYNonzero', p), f'NotRepYNonzero {t} {c} ({p} ^ 2)')}))"
          if f else "(fun h => absurd h Bool.false_ne_true)")
    return (f"(.cons (by decide +kernel : {ha}) (by decide +kernel : {hb})\n      {pairs}\n      {hc}\n      "
            + lean_cert_term(t, c, rest, override) + ")")


def lean_cert(m, h, ch, name=None, override=None):
    t, c, d = tcd(m)
    name = name or f"cert_{m}"
    desc = " ".join(f"{p}{'+' if f else ''}" for p, _, f in ch)
    return (f"/-- m = {m}, d = {d}, t = {t}, c = {c}, h = {h}: chosen {desc}. -/\n"
            f"theorem {name} : ClassCert {t} {c} {lean_list(ch)} :=\n  {lean_cert_term(t, c, ch, override)}\n")


def emit_chunk(k, ms, H, certs):
    L = ["import HCN.Finite.ClassLower", "",
         f"/-! HCN.Finite.Certs.Chunk{k}: the `h >= 3` certificates for {ms[0]} <= m <= {ms[-1]} ({len(ms)} radicands).",
         "Generated by hcn/certificates/gen_certs.py (do not edit). Every hypothesis is decided by the kernel. -/",
         "", "namespace HCN.Finite.Certs", "", "open HCN.Finite CN1.Finite", ""]
    for m in ms:
        L.append(lean_cert(m, H[tcd(m)[2]], certs[m]))
    L.append("/-- The radicands of this chunk. -/")
    L.append(f"def chunk{k} : List ℕ := [{', '.join(str(m) for m in ms)}]")
    L.append("")
    L.append("set_option maxRecDepth 8192 in")
    L.append(f"theorem exists_cert_chunk{k} : ∀ m ∈ chunk{k}, ∃ ps, ClassCert (tOf m) (cOf m) ps ∧ 2 ≤ weight ps := by")
    L.append("  intro m hm")
    L.append(f"  simp only [chunk{k}, List.mem_cons, List.mem_nil_iff, or_false] at hm")
    L.append("  rcases hm with " + " | ".join(["rfl"] * len(ms)))
    L.append("  exacts [" + ", ".join(f"⟨_, cert_{m}, by decide⟩" for m in ms) + "]")
    L.append("")
    L.append("end HCN.Finite.Certs")
    L.append("")
    return "\n".join(L)


def emit_aggregate(nchunks, ms):
    L = ["import HCN.Finite.ClassLower"]
    L += [f"import HCN.Finite.Certs.Chunk{k}" for k in range(1, nchunks + 1)]
    L += ["", "/-!",
          "# HCN.Finite.Certs: the 1,429 bridge-free `h >= 3` certificates, assembled",
          "",
          "Generated by hcn/certificates/gen_certs.py (do not edit). `hcnGe3` is the list of squarefree radicands `m`",
          f"with `dOf m <= {DMAX}` and class number at least three (COMPUTED by three reduced-form counts); each has a",
          "certificate of chosen primes with `weight = 2`, i.e. exactly the claim `h >= 3`.",
          "-/", "", "open NumberField Module CN1.Finite", "", "namespace HCN.Finite.Certs", ""]
    L.append(f"/-- The {len(ms)} squarefree radicands `m` with `dOf m ≤ {DMAX}` and `h(-dOf m) ≥ 3`. -/")
    L.append("def hcnGe3 : List ℕ := " + " ++ ".join(f"chunk{k}" for k in range(1, nchunks + 1)))
    L.append("")
    L.append(f"theorem length_hcnGe3 : hcnGe3.length = {len(ms)} := by decide +kernel")
    L.append("")
    L.append("theorem exists_cert_of_mem : ∀ m ∈ hcnGe3, ∃ ps, ClassCert (tOf m) (cOf m) ps ∧ 2 ≤ weight ps := by")
    L.append("  unfold hcnGe3")
    expr = "exists_cert_chunk1"
    for k in range(2, nchunks + 1):
        expr = f"List.forall_mem_append.mpr ⟨{expr}, exists_cert_chunk{k}⟩"
    L.append(f"  exact {expr}")
    L.append("")
    L.append("/-- **The finite lower bound, assembled.** For `K` of degree two containing `√-m`, `m` squarefree and")
    L.append("in `hcnGe3`, the class number is at least three. -/")
    L.append("theorem three_le_classNumber_of_mem {K : Type*} [Field K] [NumberField K] (hK : finrank ℚ K = 2)")
    L.append("    {m : ℕ} (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hmem : m ∈ hcnGe3) :")
    L.append("    3 ≤ classNumber K := by")
    L.append("  obtain ⟨ps, hps, hw⟩ := exists_cert_of_mem m hmem")
    L.append("  have := HCN.Finite.le_classNumber_of_cert_foundations hK hm hsq hps")
    L.append("  omega")
    L.append("")
    L.append("end HCN.Finite.Certs")
    L.append("")
    return "\n".join(L)


# ---------------------------------------------------------------- the forcing adapter (negative controls only)

def emit_forced(outdir):
    """Claim side (d = 8 and d = 15) and witness side (d = 23, TRUE claim). Each file states a certificate
    with weight 2 that the honest generator refuses; each must FAIL to build. The names are `forced_*`, never a
    target name."""
    os.makedirs(outdir, exist_ok=True)
    hdr = ["import HCN.Finite.ClassLower", "", "namespace HCN.Finite.NegControls", "", "open HCN.Finite", ""]
    files = {}
    # d = 8 (m = 2, h = 1): the least split prime is 3 (r = 1), and Q = x^2 + 2y^2 represents 3 = Q(1, 1).
    m = 2; t, c, d = tcd(m)
    assert certificate(m) is None and split_ok(t, c, 3, 1) and not notrep(t, c, 3)
    files["claim_d8.lean"] = lean_cert(m, 1, [(3, 1, True)], name="forced_cert_d8")
    # d = 15 (m = 15, h = 2): 2 splits (r = 0), NotRep(2) holds, but Q(0, 1) = 4 = 2^2, so (c) fails; forced flag true.
    m = 15; t, c, d = tcd(m)
    assert certificate(m) is None and split_ok(t, c, 2, 0) and notrep(t, c, 2) and not notrep_y(t, c, 4)
    files["claim_d15.lean"] = lean_cert(m, 2, [(2, 0, True)], name="forced_cert_d15")
    # d = 23 (m = 23, h = 3, claim TRUE): honest certificate [(2, 0, true)].
    m = 23; t, c, d = tcd(m)
    assert certificate(m) == [(2, 0, True)]
    files["witness_honest_d23.lean"] = lean_cert(m, 3, [(2, 0, True)], name="honest_cert_d23")
    # (i) its NotRep instance changed from n = 2 to n = 6 = c (Q(0, 1) = 6).
    assert not notrep(t, c, 6)
    files["witness_d23_n6.lean"] = lean_cert(m, 3, [(2, 0, True)], name="forced_cert_d23_n6",
                                                 override={("NotRep", 2): f"NotRep {t} {c} 6"})
    # (ii) the ramified prime 23 declared as the chosen prime (root r = 0 mod 23 is wrong anyway; 23 | d).
    r23 = [r for r in range(23) if (r * r + c - t * r) % 23 == 0][0]
    assert not split_ok(t, c, 23, r23)
    files["witness_d23_ramified.lean"] = lean_cert(m, 3, [(23, r23, True)], name="forced_cert_d23_ramified")
    for name, body in files.items():
        open(os.path.join(outdir, name), "w").write("\n".join(hdr) + body + "\nend HCN.Finite.NegControls\n")
    print(f"forced controls written to {outdir}: {sorted(files)}")


# ---------------------------------------------------------------- main

def main():
    args = sys.argv[1:]
    chunk = 100
    if "--chunk" in args:
        chunk = int(args[args.index("--chunk") + 1])
    if "--force-controls" in args:
        emit_forced(args[args.index("--force-controls") + 1])
        return
    H = load_h()
    print(f"class numbers: {len(H)} fundamental d <= {DMAX}; forms count = independent count = in-script count")
    ms = []
    for d in sorted(H):
        if H[d] <= TARGET:
            continue
        m = d if d % 2 else d // 4
        assert squarefree(m) and tcd(m)[2] == d, d
        ms.append(m)
    ms.sort()
    listed = [int(x) for x in open(RADLIST).read().split()]
    assert ms == sorted(listed), "radicand list differs from gen_sets.py's"
    certs, hyps, wit, pmax, dist = {}, 0, 0, 0, {}
    for m in ms:
        ch = certificate(m)
        assert ch is not None, ("no certificate", m)
        assert weight(ch) == TARGET, ("certifies more or less than the claim", m, ch)
        assert 1 + weight(ch) <= H[tcd(m)[2]], ("over-certified", m)
        t, c, d = tcd(m)
        check_true(t, c, ch)
        certs[m] = ch
        hy = hyps_of(ch)
        wit += sum(1 for k, _ in hy if k == "SplitW")
        hyps += sum(1 for k, _ in hy if k != "SplitW")
        pmax = max(pmax, max(p for p, _, _ in ch))
        dist[len(ch)] = dist.get(len(ch), 0) + 1
    # the comparison file (re-derived here; must agree exactly)
    ref = {}
    for row in csv.reader(open(f"{DATA}/cert_norm_4777.csv")):
        if row[0].isdigit():
            ref[int(row[0])] = row[3].split()
    mine = {tcd(m)[2]: [f"{p}{'+' if f else ''}" for p, _, f in certs[m]] for m in ms}
    assert mine == ref, "re-derived certificates differ from cert_norm_4777.csv"
    got = dict(certs=len(certs), hyps=hyps, witnesses=wit, pmax=pmax)
    print(f"certificates {len(certs)}; chosen-prime distribution {sorted(dist.items())}; "
          f"NotRep/NotRepYNonzero hypotheses {hyps}; split witnesses {wit}; largest prime {pmax}")
    print("agrees with cert_norm_4777.csv on every d: True")
    assert got == EXPECT, (got, EXPECT)
    print(f"matches the recorded counts {EXPECT}: True")
    # emission
    os.makedirs(f"{OUT}/Certs", exist_ok=True)
    chunks = [ms[i:i + chunk] for i in range(0, len(ms), chunk)]
    for k, cm in enumerate(chunks, 1):
        open(f"{OUT}/Certs/Chunk{k}.lean", "w").write(emit_chunk(k, cm, H, certs))
    open(f"{OUT}/Certs.lean", "w").write(emit_aggregate(len(chunks), ms))
    print(f"wrote {len(chunks)} chunk files (<= {chunk} certificates each) and Certs.lean under {OUT}")


if __name__ == "__main__":
    main()
