#!/usr/bin/env python3
"""Emit the bridge-lite data for the 18 fields with class number two as Lean.

Output: <out>/HCN/Finite/ClassTwo.lean (do not edit by hand). Usage: python3 gen_classtwo.py <out>
(or --force-controls OUTDIR).

The 18 radicands are GENERATED from the COMPUTED class numbers (classno_340000_forms.csv.gz, cross-checked against
the independent count and against gen_certs.py's in-script reduced-form count), never typed, and compared with the
list that gen_sets.py printed (<out>/gen_sets_out.txt).

Per field m (t = tOf m, c = cOf m, d = dOf m), consumed by HCN.Finite.classNumber_eq_two_of_bridge:
  * B: the least B with 4d < 9 B^2, so the Minkowski bound (<= (2/3) sqrt d) is < B;
  * q0: the least prime q0 | d (ramified: X^2 - tX + c has the unique root z0 mod q0) with NotRep(q0), so that
    g = [P_{q0}] has g != 1 and g^2 = 1;
  * W: for every prime q < B and every root z < q of X^2 - tX + c mod q, other than (q0, z0), a positive witness
    (x, y): Q(x, y) = q and q | x + y z (the prime "(q, theta - z)" is principal), or else Q(x, y) = q q0,
    q | x + y z and q0 | x + y z0 (its class is g^{-1} = g).
Every check is repeated here before emission; the kernel re-decides the whole BridgeCert.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_certs as G

OUT = os.path.join(G.OUTDIR, "HCN", "Finite", "ClassTwo.lean")
SETS_LOG = os.path.join(G.OUTDIR, "gen_sets_out.txt")


def Q(t, c, x, y):
    return x * x + t * x * y + c * y * y


def roots(t, c, q):
    return [z for z in range(q) if (z * z - t * z + c) % q == 0]


def find(t, c, n, conds, box=60):
    for s in range(0, 2 * box + 1):
        for y in range(-box, box + 1):
            for x in (s, -s) if s else (0,):
                if Q(t, c, x, y) == n and all((x + y * z) % qq == 0 for qq, z in conds):
                    return x, y
    return None


def field_data(m):
    t, c, d = G.tcd(m)
    B = 1
    while not 4 * d < 9 * B * B:
        B += 1
    q0 = None
    for q in G.PRIMES:
        if q > d:
            break
        if d % q == 0 and len(roots(t, c, q)) == 1 and G.notrep(t, c, q):
            q0 = q
            break
    assert q0 is not None, ("no nonprincipal ramified prime", m)
    z0 = roots(t, c, q0)[0]
    W = []
    for q in range(2, B):
        if not G.is_prime(q):
            continue
        for z in roots(t, c, q):
            if q == q0:
                assert z == z0
                continue
            w = find(t, c, q, [(q, z)])
            if w is not None:
                W.append((q, z, w[0], w[1], False))
                continue
            assert q != q0
            w = find(t, c, q * q0, [(q, z), (q0, z0)])
            assert w is not None, ("no witness", m, q, z)
            W.append((q, z, w[0], w[1], True))
    return t, c, d, B, q0, z0, W


def check(t, c, d, B, q0, z0, W):
    """Mirror of the Lean BridgeCert."""
    assert G.is_prime(q0) and z0 < q0 and (z0 * z0 - t * z0 + c) % q0 == 0
    assert all((z * z - t * z + c) % q0 != 0 or z == z0 for z in range(q0))
    for q in range(B):
        if not G.is_prime(q):
            continue
        for z in range(q):
            if (z * z - t * z + c) % q != 0 or q == q0:
                continue
            ok = False
            for (wq, wz, x, y, g) in W:
                if wq != q or wz != z or (x + y * z) % q != 0:
                    continue
                if g:
                    ok |= Q(t, c, x, y) == q * q0 and (x + y * z0) % q0 == 0 and q != q0
                else:
                    ok |= Q(t, c, x, y) == q
            assert ok, (q, z)
    assert 4 * d < 9 * B * B
    assert G.notrep(t, c, q0)


def emit_forced(outdir):
    """Bridge-side negative controls (forcing adapter; never under the Lean library): class number two FORCED for
    m = 431 (h = 21; the 427 -> 431 claim control) and m = 23 (h = 3). In both, the only ramified
    prime is principal and a split prime below B has no witness, so BridgeCert and NotRep(q0) are false; each file
    must FAIL to build. Names are `forced_*`, never a target name."""
    os.makedirs(outdir, exist_ok=True)
    for m, h in ((431, 21), (23, 3)):
        t, c, d = G.tcd(m)
        B = 1
        while not 4 * d < 9 * B * B:
            B += 1
        q0 = m
        z0 = roots(t, c, q0)[0]
        assert len(roots(t, c, q0)) == 1 and not G.notrep(t, c, q0)
        body = ["import HCN.Finite.IdealLite", "", "namespace HCN.Finite.NegControls", "",
                "open NumberField Module HCN.Finite", "",
                f"/-- FORCED: m = {m}, d = {d}, h = {h}; q0 = {q0} (principal), no witnesses. Must fail. -/",
                f"theorem forced_classNumber_eq_two_{m} {{K : Type*}} [Field K] [NumberField K] (hK : finrank ℚ K = 2)",
                f"    (hm : Squarefree {m}) (hsq : ∃ α : K, α ^ 2 = -(({m} : ℕ) : K)) : classNumber K = 2 :=",
                f"  classNumber_eq_two_of_bridge hK hm hsq (B := {B}) (q0 := {q0}) (z0 := {z0})",
                "    (W := [])",
                "    (by decide +kernel) (by decide +kernel) (by decide +kernel)", "",
                "end HCN.Finite.NegControls", ""]
        open(os.path.join(outdir, f"bridge_forced_{m}.lean"), "w").write("\n".join(body))
    print(f"forced bridge controls written to {outdir}")


def main():
    if "--force-controls" in sys.argv:
        emit_forced(sys.argv[sys.argv.index("--force-controls") + 1])
        return
    H = G.load_h()
    ms = sorted((d if d % 2 else d // 4) for d in H if H[d] == 2)
    assert len(ms) == 18
    listed = None
    for line in open(SETS_LOG):
        if line.startswith("h = 2 radicands"):
            listed = [int(x) for x in line.split("[")[1].split("]")[0].split(",")]
    assert listed == ms, (listed, ms)
    print(f"h = 2 radicands (18), from the data, = gen_sets.py's list: {ms}")
    L = ["import HCN.Finite.IdealLite", "",
         "/-!",
         "# HCN.Finite.ClassTwo: the 18 imaginary quadratic fields with class number two",
         "",
         "Generated by hcn/certificates/gen_classtwo.py (do not edit). For each radicand `m` with `h(-dOf m) = 2`",
         "(COMPUTED; the set is generated from the class-number data, never typed), a bridge certificate: the bound `B`",
         "with `4·dOf m < 9·B²`, a nonprincipal ramified prime `q₀` with its unique root `z₀`, and a positive witness",
         "for every other prime `(q, θ - z)` with `q < B`. All checks are decided by the kernel.",
         "-/", "", "open NumberField Module CN1.Finite", "", "namespace HCN.Finite.ClassTwo", "",
         "open HCN.Finite", ""]
    names = []
    total_w = 0
    for m in ms:
        t, c, d, B, q0, z0, W = field_data(m)
        check(t, c, d, B, q0, z0, W)
        total_w += len(W)
        wl = "[" + ", ".join(f"⟨{q}, {z}, {x}, {y}, {'true' if g else 'false'}⟩" for q, z, x, y, g in W) + "]"
        print(f"  m = {m}: d = {d}, t = {t}, c = {c}, B = {B}, q0 = {q0}, z0 = {z0}, witnesses {len(W)} "
              f"({sum(1 for w in W if not w[4])} principal, {sum(1 for w in W if w[4])} in g)")
        L.append(f"/-- m = {m}, d = {d}, t = {t}, c = {c}: `B = {B}`, `q₀ = {q0}`, `z₀ = {z0}`, "
                 f"{len(W)} witnesses. -/")
        L.append(f"theorem classNumber_eq_two_{m} {{K : Type*}} [Field K] [NumberField K] (hK : finrank ℚ K = 2)")
        L.append(f"    (hm : Squarefree {m}) (hsq : ∃ α : K, α ^ 2 = -(({m} : ℕ) : K)) : classNumber K = 2 :=")
        L.append(f"  classNumber_eq_two_of_bridge hK hm hsq (B := {B}) (q0 := {q0}) (z0 := {z0})")
        L.append(f"    (W := {wl})")
        L.append(f"    (by decide +kernel) (by decide +kernel) (by decide +kernel)")
        L.append("")
        names.append(m)
    L.append(f"/-- The 18 radicands with class number two. -/")
    L.append("def classTwo18 : Finset ℕ := {" + ", ".join(str(m) for m in ms) + "}")
    L.append("")
    L.append("/-- **Class number two for the 18 fields.** -/")
    L.append("theorem classNumber_eq_two_of_mem {K : Type*} [Field K] [NumberField K] (hK : finrank ℚ K = 2)")
    L.append("    {m : ℕ} (hm : Squarefree m) (hsq : ∃ α : K, α ^ 2 = -(m : K)) (hmem : m ∈ classTwo18) :")
    L.append("    classNumber K = 2 := by")
    L.append("  simp only [classTwo18, Finset.mem_insert, Finset.mem_singleton] at hmem")
    L.append("  rcases hmem with " + " | ".join(["rfl"] * len(ms)))
    L.append("  exacts [" + ", ".join(f"classNumber_eq_two_{m} hK hm hsq" for m in ms) + "]")
    L.append("")
    L.append("end HCN.Finite.ClassTwo")
    L.append("")
    open(OUT, "w").write("\n".join(L))
    print(f"total witnesses {total_w}; wrote {OUT}")


if __name__ == "__main__":
    main()
