"""Tests for the tie-regime campaign: the uniform-hub potential + the arithmetic cherry-worst reduction.

Verifies: uniform_hub_ell(k, cherry) == branch ell(B(k)); the envelope tops are brooms; the cherry-worst
rational ratio > 1 (slack) in the tie regime; ell(hub of k cherries) has its max = 0 at k=5.
conjecture1_proved = False.
"""
import math
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from telperion.branch_potential import branch_ell, broom_edges  # noqa: E402
from telperion.tie_regime import (  # noqa: E402
    CHERRY,
    TieCherryWorstCertificate,
    binding_j,
    broom_child,
    cherry_vs_broom_ratio,
    uniform_hub_ell,
)


def test_uniform_cherry_hub_is_broom():
    """ell(hub of k cherries) == branch ell(B(k)) (the broom), to float precision."""
    for k in range(1, 9):
        ell_uniform = uniform_hub_ell(k, CHERRY)
        ell_broom, _ = branch_ell(*broom_edges(k))
        assert abs(ell_uniform - ell_broom) < 1e-9, f"k={k}"


def test_broom_hub_max_at_5():
    """max_k ell(hub of k cherries) = 0 at k=5 (the tie); strictly negative elsewhere -- the broom optimum (B)."""
    vals = {k: uniform_hub_ell(k, CHERRY) for k in range(1, 12)}
    assert max(vals, key=vals.get) == 5
    assert abs(vals[5]) < 1e-9
    for k in range(1, 5):
        assert vals[k] < -1e-9
    for k in range(6, 12):
        assert vals[k] < -1e-9


def test_cherry_worst_rational_and_slack():
    """cherry-worst: exp(11*(ell(k,cherry)-ell(k,B(j)))) is EXACT rational and > 1 (slack, >= 2) in the tie
    regime -- so the cherry is the worst uniform child with margin (only the broom step is tie-tight)."""
    for k in range(2, 8):
        for j in range(2, 8):
            r = cherry_vs_broom_ratio(k, j)
            assert isinstance(r, Fr)
            assert r > 1, f"cherry not worst at k={k}, j={j}"
            assert r > Fr(3, 2), f"expected slack (>1.5) at k={k}, j={j}, got {float(r)}"  # min ~1.95 at (2,2)


def test_cherry_beats_broom_children_ell():
    """Directly: ell(hub of k cherries) >= ell(hub of k B(j)) for tie-regime k (cherry is the worst child)."""
    for k in range(1, 9):
        ec = uniform_hub_ell(k, CHERRY)
        for j in range(2, 10):
            assert ec >= uniform_hub_ell(k, broom_child(j)) - 1e-12, f"k={k}, j={j}"


def test_ratio_unimodal_in_j_and_binding():
    """cherry_vs_broom_ratio(k, .) is unimodal in j (min at binding_j(k)); ratio(k, j*) > 1 covers all j."""
    for k in range(2, 21):
        js = binding_j(k)
        vals = {j: cherry_vs_broom_ratio(k, j) for j in range(1, 25)}
        assert min(vals, key=vals.get) == js
        assert all(vals[j] > vals[j + 1] for j in range(1, js))       # decreasing to j*
        assert all(vals[j] < vals[j + 1] for j in range(js, 24))      # increasing after j*
        assert vals[js] > 1                                            # binding case still cherry-worst


def test_tie_cherry_worst_certificate_k20():
    """The k<=20 certificate holds exactly and emits a well-formed norm_num module (19 atoms)."""
    cert = TieCherryWorstCertificate(k_max=20)
    assert cert.check() is True
    assert len(cert.atoms()) == 19
    mod = cert.lean_module()
    assert "import Mathlib" in mod and "namespace BGTieCherryWorst" in mod
    assert mod.count("by norm_num") == 19
    # k=21 is outside the tie regime -- the certificate must NOT claim it
    assert cherry_vs_broom_ratio(21, 4) < 1


def _hub(children):
    """Build a hub (root 0) from a list of child specs and return its exact ell."""
    from telperion.branch_potential import branch_ell
    E = []
    nid = 1
    for spec in children:
        if spec == ("leaf",):
            E.append((0, nid)); nid += 1
        elif spec == ("cherry",):
            E.append((0, nid)); E.append((nid, nid + 1)); nid += 2
        elif spec[0] == "broom":
            hub = nid; E.append((0, hub)); nid += 1
            for _ in range(spec[1]):
                E.append((hub, nid)); E.append((nid, nid + 1)); nid += 2
    ell, _ = branch_ell(nid, tuple(E), 0)
    return ell


def test_mixed_le_uniform_k_le_15():
    """mixed <= B(k) for k in {2..15} ONLY -- it FAILS at k >= 20 (a hub of (k-1) cherries + one B(5)-child
    beats B(k); mixed - B(20) = +0.00035). The mixed reduction is used only for k <= 15; the slack bound covers
    k >= 16 (`slack_g(k) <= F*`). So no gap. (Corrects the earlier false 'k <= 20' claim -- caught by the
    child->cherry exchange analysis.)"""
    import random
    from telperion.branch_potential import branch_ell, broom_edges
    pool = [("leaf",), ("cherry",), ("broom", 2), ("broom", 4), ("broom", 5), ("broom", 6)]
    rng = random.Random(7)
    for k in range(2, 16):                                     # k <= 15 (mixed<=B(k) holds; slack covers k>=16)
        ell_bk, _ = branch_ell(*broom_edges(k))
        for _ in range(300):
            ch = [rng.choice(pool) for _ in range(k)]
            assert _hub(ch) <= ell_bk + 1e-12, f"mixed hub beats B({k})"
        for a in range(k + 1):
            assert _hub([("leaf",)] * a + [("cherry",)] * (k - a)) <= ell_bk + 1e-12
    # the failure at k=20 is REAL and must be recorded (not asserted away):
    mix20 = _hub([("cherry",)] * 19 + [("broom", 5)])
    ell_b20, _ = branch_ell(*broom_edges(20))
    assert mix20 > ell_b20                                     # mixed BEATS B(20) -- reduction fails here
    assert mix20 < 0                                           # but the BOUND ell <= 0 still holds


def test_slack_regime_bound():
    """Slack regime k>=21: ell(hub) <= slack_hub_bound(k) <= 0 (tie-free soft bound); sup at k=21."""
    from telperion.tie_regime import slack_hub_bound, slack_g
    for k in [21, 22, 25, 30, 50, 100, 500]:
        assert slack_hub_bound(k) < 0, f"slack bound not < 0 at k={k}"
        assert slack_g(k) < 0.207, f"g(k) not < F* at k={k}"
    # tightest at the boundary k=21, with margin ~0.05
    assert -0.06 < slack_hub_bound(21) < -0.04


def test_slack_certificate():
    """TieSlackCertificate: the slack bound slack_g(k)<=F* (k>=16) via frozen log-enclosures -- checks exactly
    and emits a well-formed norm_num module (phi16 + deriv16 + F*>3/23 atoms)."""
    from telperion.tie_regime import TieSlackCertificate
    cert = TieSlackCertificate()
    assert cert.check() is True
    names = [a[0] for a in cert.atoms()]
    assert sum("phi16" in n for n in names) == 8                # slack_g(16)<F* per envelope child
    assert sum("deriv16" in n for n in names) == 7              # monotone (non-B(5))
    assert "tie_slack_Fstar_gt_3_23" in names                   # B(5) bound
    mod = cert.lean_module()
    assert "import Mathlib" in mod and mod.count("by norm_num") == len(cert.atoms())


def test_mixed_kkt_reduction_concavity():
    """The concavity tangent bound is EXACT (never violated): for arbitrary mixed hubs,
    ell(hub) - ell(B(k)) <= sum_i (V(c_i) - V(cherry)), V(c)=ell(c)+lambda(k) x_c, lambda(k)=3(k+1)/(4k+3).
    This is the rigorous log-concavity step that decouples the mixed-hub bound into per-child inequalities."""
    import random
    from telperion.branch_potential import branch_ell, broom_edges
    from telperion.tie_regime import mixed_lambda, child_value, CHERRY, broom_child
    from fractions import Fraction as Fr

    # lambda(k) = 3(k+1)/(4k+3) exact (derivative of log(1+.) at the all-cherry point)
    assert mixed_lambda(5) == Fr(18, 23)

    specs = {("cherry",): CHERRY, ("broom", 2): broom_child(2), ("broom", 4): broom_child(4),
             ("broom", 5): broom_child(5), ("broom", 6): broom_child(6)}
    rng = random.Random(11)
    for k in range(2, 16):
        ell_bk, _ = branch_ell(*broom_edges(k))
        vch = child_value(CHERRY, k)
        for _ in range(200):
            ch = [rng.choice(list(specs)) for _ in range(k)]
            ell_hub = _hub(ch)
            rhs = sum(child_value(specs[c], k) - vch for c in ch)          # sum (V(c_i) - V(cherry))
            assert ell_hub - ell_bk <= rhs + 1e-12                          # concavity tangent (rigorous)
            assert rhs <= 1e-9                                              # per-child KKT => sum <= 0


def test_mixed_hub_kkt_certificate():
    """MixedHubKKTCertificate: per-child V(c) < V(cherry) for every broom child and k in [2,15], via frozen
    log-enclosures -- proving (with concavity) mixed <= B(k) for k <= 15. Checks exact + emits norm_num."""
    from telperion.tie_regime import MixedHubKKTCertificate, cherry_is_kkt_argmax
    cert = MixedHubKKTCertificate()
    assert cert.check() is True
    assert len(cert.atoms()) == 14 * 7                                      # k=2..15 x B(2..8)
    # KKT (cherry = argmax V over the broom envelope) holds across the whole tie regime k<=15 ...
    assert all(cherry_is_kkt_argmax(k) for k in range(2, 16))
    # ... and must FAIL for large k (else it would contradict mixed<=B(k) itself failing at k>=20)
    assert not cherry_is_kkt_argmax(20)
    mod = cert.lean_module()
    assert "import Mathlib" in mod and "namespace BGMixedHubKKT" in mod
    assert mod.count("by norm_num") == len(cert.atoms())


def test_high_degree_tail_certificate():
    """HighDegreeTailCertificate: for d_c >= 7 the per-child envelope V(c) < V(cherry) holds using ONLY the
    ceiling ell(c)<=0 and h_c<=1 -- reduces to -44/(7(4k+3)) < 11 ell(cherry), gated via log-enclosures. This
    shrinks the open envelope tail to small-degree (d_c<=6) branches. Also verifies the bound empirically."""
    import math
    import networkx as nx
    from fractions import Fraction as Fr
    from telperion.tie_regime import HighDegreeTailCertificate, F_STAR, mixed_lambda, CHERRY, child_value
    from telperion.bg_bulk_discharge import _adj

    cert = HighDegreeTailCertificate()
    assert cert.check() is True
    assert len(cert.atoms()) == 14                                          # k=2..15
    mod = cert.lean_module()
    assert "namespace BGHighDegreeTail" in mod and mod.count("by norm_num") == 14

    # empirical: every branch (size <= 12) with root branch-degree d_c >= 7 has V(c) < V(cherry) at the worst k
    def _bd(N, ee, r):
        adj = _adj(N, ee)
        def um(u, p):
            kids = [w for w in adj[u] if w != p]; d = len(kids) + 1
            ch = [(w,) + um(w, u) for w in kids]; U = Fr(1); sz = 1
            for w, Uw, Mw, tw, sw in ch: U *= tw; sz += sw
            M = Fr(0)
            for i, (w, Uw, Mw, tw, sw) in enumerate(ch):
                dw = len([q for q in adj[w] if q != u]) + 1; t = Fr(1, d * dw) * Uw
                for j2, (w2, Uw2, Mw2, tw2, sw2) in enumerate(ch):
                    if j2 != i: t *= tw2
                M += t
            return U, M, U + M, sz
        U, M, tot, sz = um(r, -1); d = len(adj[r]) + 1
        return d, float(U / tot), (math.log(tot.numerator) - math.log(tot.denominator)) - sz * F_STAR

    k = 15; lam = float(mixed_lambda(k)); vch = child_value(CHERRY, k)
    for N in range(8, 13):
        for T in nx.nonisomorphic_trees(N):
            idx = {v: i for i, v in enumerate(T.nodes())}; ee = [(idx[a], idx[b]) for a, b in T.edges()]
            for r in T.nodes():
                d, h, ell = _bd(N, ee, idx[r])
                if d >= 7:
                    assert ell + lam * h / ((k + 1) * d) < vch                # V(c) < V(cherry)


def test_envelope_tail_case_split_closes():
    """The per-child envelope tail V(c)<V(cherry) splits into three cases (hi_degree / threshold / broom), only
    one open. This verifies the split CLOSES: every branch is covered by a gated case OR the refined-ceiling
    threshold -- and whenever a branch is 'open' (small-degree, ell>=threshold) it is a BROOM (gated by
    mixed_kkt), never a non-broom residual. Checked over all branches <= size 14, generalized brooms (to size
    66), and star-of-brooms rooted at low-degree vertices (to size 101)."""
    import math
    import networkx as nx
    from fractions import Fraction as Fr
    from telperion.tie_regime import (F_STAR, mixed_lambda, CHERRY, child_value, broom_child,
                                       envelope_tail_case, small_degree_threshold, _ell_of)
    from telperion.spider_broom import spider_edges
    from telperion.bg_bulk_discharge import _adj

    k = 15
    lam = float(mixed_lambda(k)); vch = child_value(CHERRY, k)
    broom_ell = {round(_ell_of(broom_child(j)), 6) for j in range(2, 12)} | {round(_ell_of(CHERRY), 6)}

    def _bd(N, ee, r):
        adj = _adj(N, ee)
        def um(u, p):
            kids = [w for w in adj[u] if w != p]; d = len(kids) + 1
            ch = [(w,) + um(w, u) for w in kids]; U = Fr(1); sz = 1
            for w, Uw, Mw, tw, sw in ch: U *= tw; sz += sw
            M = Fr(0)
            for i, (w, Uw, Mw, tw, sw) in enumerate(ch):
                dw = len([q for q in adj[w] if q != u]) + 1; t = Fr(1, d * dw) * Uw
                for j2, (w2, Uw2, Mw2, tw2, sw2) in enumerate(ch):
                    if j2 != i: t *= tw2
                M += t
            return U, M, U + M, sz
        U, M, tot, sz = um(r, -1); d = len(adj[r]) + 1; h = float(U / tot)
        ell = (math.log(tot.numerator) - math.log(tot.denominator)) - sz * F_STAR
        return d, h, ell

    def _check(d, h, ell):
        case = envelope_tail_case(d, ell, k)
        # every covered case must actually give V(c) < V(cherry)
        if case in ("hi_degree", "threshold"):
            assert ell + lam * h / ((k + 1) * d) < vch
        else:                                                   # 'open' => must be a broom (gated), not residual
            assert round(ell, 6) in broom_ell, f"non-broom in OPEN case: d={d}, ell={ell}"

    # (i) all branches up to size 16 (>= the size-16 near-broom that exposed the single-threshold bug)
    for N in range(2, 17):
        for T in nx.nonisomorphic_trees(N):
            idx = {v: i for i, v in enumerate(T.nodes())}; ee = [(idx[a], idx[b]) for a, b in T.edges()]
            for r in T.nodes():
                _check(*_bd(N, ee, idx[r]))
    # (ii) star-of-brooms S(kc,5) rooted at every vertex (near-extremal, sizes up to ~101)
    for kc in range(2, 10):
        N, ee = spider_edges(kc, 5)
        for r in range(N):
            _check(*_bd(N, ee, r))
    # (iii) the degree-dependent threshold: d=3 == ell(cherry), d>=4 above it, d=2 below it
    assert abs(small_degree_threshold(k, 3) - _ell_of(CHERRY)) < 1e-12
    assert small_degree_threshold(k, 2) < _ell_of(CHERRY) < small_degree_threshold(k, 6)


def test_degree_dependent_threshold_regression():
    """Regression for the 11th caught overclaim: the near-broom `4 cherries + B(3)` (d=6, size 16, ell=-0.0164)
    has V(c) < V(cherry) at every k, and is correctly classified 'threshold' (covered) by the DEGREE-DEPENDENT
    threshold at every k -- whereas the old single (d=2) threshold mis-classified it 'open' at small k."""
    import math
    from fractions import Fraction as Fr
    from telperion.tie_regime import (mixed_lambda, CHERRY, child_value, broom_child, _ell_of,
                                      envelope_tail_case, small_degree_threshold)
    # build the child (4 cherries + 1 B(3)) as a degree-6 branch, exact
    A = Fr(1); s = 0.0
    kids = [CHERRY] * 4 + [broom_child(3)]
    for c in kids:
        s += _ell_of(c); A += Fr(c["h"], 1) / (6 * c["d"])          # hub degree d=6 (5 children + up-edge)
    ell = s + (math.log(A.numerator) - math.log(A.denominator)) - __import__(
        "telperion.tie_regime", fromlist=["F_STAR"]).F_STAR
    h = float(1 / A); d = 6
    assert abs(ell - (-0.0164)) < 5e-4
    for k in range(2, 16):
        V = ell + float(mixed_lambda(k)) * h / ((k + 1) * d)
        assert V < child_value(CHERRY, k)                            # actual envelope holds
        assert ell < small_degree_threshold(k, d)                    # covered by d-dependent threshold
        assert envelope_tail_case(d, ell, k) == "threshold"          # correctly classified (not 'open')


def test_slack_bound_proof_structure():
    """Rigorous proof of slack_g(k) <= F* for k>=16: (1) slack_g monotone-decreasing so <= slack_g(16);
    (2) slack_g(16) < F*; (3) per-child, every non-B(5) envelope child phi_c is decreasing for k>=16
    (deriv = ell(c) + (h/d)/(k+1)^2 < 0, and deriv <= deriv@16), and B(5) is bounded by 3/23 < F*."""
    import math
    from telperion.tie_regime import slack_g, broom_child
    from telperion.branch_potential import F_STAR
    g16 = slack_g(16)
    assert all(slack_g(k) <= g16 + 1e-12 for k in range(16, 400))   # (1) monotone-decreasing sup
    assert g16 < F_STAR                                             # (2) binding value < F*
    # (3) per-child derivative at k=16 (the largest, since (k+1)^2 grows): < 0 for non-B(5), B(5) bounded
    for j in list(range(2, 9)):
        c = broom_child(j)
        tot, sz = c["total"], c["size"]
        el = (math.log(tot.numerator) - math.log(tot.denominator)) - sz * F_STAR
        deriv16 = el + (float(c["h"]) / c["d"]) / 17 ** 2
        if j == 5:
            assert 3 / 23 < F_STAR                                 # B(5): phi -> 3/23 < F*
        else:
            assert deriv16 < 0                                     # decreasing for all k >= 16


def test_md_step_certificate():
    """MdStepCertificate (M_d frontier bound, Phase 2): the worst non-broom hub of root-degree d in {3,4,5,6}
    -- (d-2) cherries + 1 small broom -- has ell(hub) < threshold(k,d) for all k, via frozen log-enclosures.
    Gates the per-degree binding step; extremality (near-broom = max non-broom hub) is the residual."""
    from telperion.tie_regime import MdStepCertificate, y_floor, _MDHUB
    from telperion.branch_potential import branch_total
    from fractions import Fraction as Fr
    cert = MdStepCertificate()
    assert cert.check() is True
    assert len(cert.atoms()) == 4 * 14                          # d=3..6 x k=2..15
    # soundness: frozen hub totals match branch_total of the actual near-broom hubs
    for d in range(3, 7):
        E = []; nid = 1
        for _ in range(d - 2):
            E += [(0, nid), (nid, nid + 1)]; nid += 2
        hub = nid; E += [(0, hub)]; nid += 1
        for _ in range(_MDHUB[d]["j"]):
            E += [(hub, nid), (nid, nid + 1)]; nid += 2
        tot = branch_total(nid, tuple(E), 0)
        assert tot == Fr(_MDHUB[d]["num"], _MDHUB[d]["den"]) and nid == _MDHUB[d]["size"]
    # y-floor exact: y >= 1/(2d-1)
    assert y_floor(3) == Fr(1, 5) and y_floor(6) == Fr(1, 11)
    mod = cert.lean_module()
    assert "namespace BGMdStep" in mod and mod.count("by norm_num") == len(cert.atoms())


def test_monotone_tail_certificate():
    """MonotoneTailCertificate (M_d Phase 3): any non-broom hub of degree d in {3,4,5,6} with a child of
    degree >= 7 has ell(hub) < threshold(k,d), RIGOROUSLY via concavity + HighDegreeTail + broom optimum
    (no enumeration). Cleared atom: 11 L(total B(d-1)) - 22 L(3/2) - (2d-5) L(621/64) < 11[4/7+(d-3)/d]/(4k+3).
    So the M_d induction restricts to d_i<=6 children (finite)."""
    from telperion.tie_regime import MonotoneTailCertificate, small_degree_threshold
    import math
    from telperion.branch_potential import branch_total, F_STAR
    cert = MonotoneTailCertificate()
    assert cert.check() is True
    assert len(cert.atoms()) == 4 * 14
    # empirical soundness: actual hubs (d-2 cherries + 1 B(6), child degree 7) are all < threshold
    def ell_hub(d, j):
        E = []; nid = 1
        for _ in range(d - 2):
            E += [(0, nid), (nid, nid + 1)]; nid += 2
        hub = nid; E += [(0, hub)]; nid += 1
        for _ in range(j):
            E += [(hub, nid), (nid, nid + 1)]; nid += 2
        t = branch_total(nid, tuple(E), 0)
        return (math.log(t.numerator) - math.log(t.denominator)) - nid * F_STAR
    for d in range(3, 7):
        assert ell_hub(d, 6) < min(small_degree_threshold(k, d) for k in range(2, 16))
    mod = cert.lean_module()
    assert "namespace BGMdTail" in mod and mod.count("by norm_num") == len(cert.atoms())


def test_free_closure_certificate():
    """FreeClosureCertificate (M_d): degrees d in {3,4,6} close FREE -- the concavity ceiling ell(hub)<=ell(B(d-1))
    already beats threshold(k,d), no extremality needed. ell(B(d-1)) < threshold(k,d) cleared via enclosures.
    d=5 does NOT close free (residual). This localizes the whole M_d wall to a single degree."""
    from telperion.tie_regime import FreeClosureCertificate, small_degree_threshold
    from telperion.branch_potential import branch_ell, broom_edges
    cert = FreeClosureCertificate()
    assert cert.check() is True
    assert len(cert.atoms()) == 3 * 14                          # d in {3,4,6} x k=2..15
    # soundness: ell(B(d-1)) really < min_k threshold(k,d) for d in {3,4,6}, and NOT for d=5
    for d in (3, 4, 6):
        eB, _ = branch_ell(*broom_edges(d - 1))
        assert eB < min(small_degree_threshold(k, d) for k in range(2, 16))
    eB5, _ = branch_ell(*broom_edges(4))
    assert eB5 >= min(small_degree_threshold(k, 5) for k in range(2, 16))   # d=5 does NOT close free
    mod = cert.lean_module()
    assert "namespace BGMdFree" in mod and mod.count("by norm_num") == len(cert.atoms())


def test_md_geometric_tail_certificate():
    """MdGeometricTailCertificate (M_d): gates the FINITE arithmetic of the whole M_d frontier closure, conditional
    on the one open lemma (even-step ell-subsequence contraction rho<=5/12). Peaked degrees d=2..5 (max at interior
    sizes 4,6,10,14) close directly; d=6 (still climbing at the size-16 boundary) closes via the geometric tail."""
    from telperion.tie_regime import MdGeometricTailCertificate, small_degree_threshold, _MDGEO, _MDGEO_DELTA
    from telperion.branch_potential import F_STAR
    from fractions import Fraction as Fr
    import math
    cert = MdGeometricTailCertificate()
    assert cert.check() is True
    assert cert.rho == Fr(5, 12)
    assert len(cert.atoms()) == 5 * 14                                   # d in {2,3,4,5} peaks + d=6 tail, k=2..15
    # soundness: each peaked-degree total's ell really < min_k threshold(k,d), with margin
    for d in (2, 3, 4, 5):
        p, q = _MDGEO[d]["total"]; sz = _MDGEO[d]["size"]
        ell = (math.log(p) - math.log(q)) - sz * F_STAR
        assert ell < float(min(small_degree_threshold(k, d) for k in range(2, 16)))
    # d=6 geometric-tail limit: ell(6,16) + (5/7)*Delta < threshold(6), Delta = L(delta_ratio) - 2 F*
    p6, q6 = _MDGEO[6]["total"]; dp, dq = _MDGEO_DELTA
    ell16 = (math.log(p6) - math.log(q6)) - 16 * F_STAR
    delta = (math.log(dp) - math.log(dq)) - 2 * F_STAR
    limit = ell16 + (5.0 / 7.0) * delta
    assert limit < float(min(small_degree_threshold(k, 6) for k in range(2, 16)))
    mod = cert.lean_module()
    assert "namespace BGMdGeoTail" in mod and mod.count("by norm_num") == len(cert.atoms())


def test_near_broom_unimodality_certificate():
    """NearBroomUnimodalityCertificate (M_d): the near-broom family (d-2)cherries+B(m) peaks at m*=max(1,d-3) and
    STRICTLY DECREASES after -- so M_d(near-broom) is the FINITE peak, UNCONDITIONALLY (no rho<=5/12, no infinite
    tail). Pure-rational atoms: BIG(d,m*)^11 < (621/64)^2 (peak), BIG(d,m*-1)^11 > (621/64)^2 (peak-loc),
    monotone-tail Handelman coeffs > 0, (3/2)^11 < (621/64)^2 (d=2 tail)."""
    from telperion.tie_regime import (
        NearBroomUnimodalityCertificate, _nearbroom_BIG, _NEARBROOM_MSTAR, small_degree_threshold,
    )
    from telperion.branch_potential import F_STAR
    from fractions import Fraction as Fr
    import math
    cert = NearBroomUnimodalityCertificate()
    assert cert.check() is True
    assert len(cert.atoms()) == 17
    tgt = Fr(621, 64) ** 2
    # peak is a genuine local max (Delta(d,m*)<0) and the peak is exactly m* (Delta(d,m*-1)>0 for m*>1)
    for d in range(2, 7):
        ms = _NEARBROOM_MSTAR[d]
        assert _nearbroom_BIG(d, ms) ** 11 < tgt
        if ms > 1:
            assert _nearbroom_BIG(d, ms - 1) ** 11 > tgt
    # BIG strictly decreasing on the ray past m* => ell strictly decreasing (spot-check far out)
    for d in (3, 4, 5, 6):
        ms = _NEARBROOM_MSTAR[d]
        assert _nearbroom_BIG(d, ms + 50) > _nearbroom_BIG(d, ms + 51)
    # the finite peak really is < threshold(d) (this is the M_d value for the near-broom family)
    def ell_nb(d, m):
        ELLC = math.log(1.5) - 2 * F_STAR
        s = Fr(d - 2, 3) + Fr(3, 4 * m + 3)
        return (d - 2 + m) * ELLC + math.log((4 * m + 3) / (3 * (m + 1))) + math.log(1 + float(s) / d) - 2 * F_STAR
    for d in range(2, 7):
        ms = _NEARBROOM_MSTAR[d]
        assert ell_nb(d, ms) < float(min(small_degree_threshold(k, d) for k in range(2, 16)))
    mod = cert.lean_module()
    assert "namespace BGNearBroomUnimodal" in mod and mod.count("by norm_num") == len(cert.atoms())


def test_extremality_price_map_certificate():
    """ExtremalityPriceMapCertificate: the single-child lemma's joint size-induction has its prices confined to the
    invariant interval I=[456/3703,3/7]. The concavity-tangent price map mu''=3[(4d-1)-3mu]/(4d-1)^2 keeps I
    invariant for hub-degrees 2..6, and all actual hub prices mu_d=3/(4d-1) lie in I. Pure exact rational."""
    from telperion.tie_regime import ExtremalityPriceMapCertificate, _price_map, _EXTREMALITY_I
    from fractions import Fraction as Fr
    cert = ExtremalityPriceMapCertificate()
    assert cert.check() is True
    assert len(cert.atoms()) == 20
    A, B = _EXTREMALITY_I
    # invariance: mu'' (decreasing in mu) maps [A,B] into [A,B] for d=2..6
    for d in range(2, 7):
        assert _price_map(d, B) >= A and _price_map(d, A) <= B
        assert A <= Fr(3, 4 * d - 1) <= B
    # A is the fixed point of the tightest (d=6) map
    assert _price_map(6, B) == A
    mod = cert.lean_module()
    assert "namespace BGExtremalityPriceMap" in mod and mod.count("by norm_num") == len(cert.atoms())


def test_broom_vs_cherry_on_I_certificate():
    """BroomVsCherryOnICertificate (extremality leg #4): V_mu(B(j)) <= V_mu(cherry) for every broom child of
    degree <= 6 (j=1..5) UNIFORMLY on I=[456/3703,3/7] (linear in mu -> both endpoints suffice). Cleared to
    log-enclosure atoms 11 L(total B(j)) - 11 L(3/2) - (2j-1) L(621/64) < 11 mu (1/3 - y_Bj)."""
    from telperion.tie_regime import BroomVsCherryOnICertificate
    cert = BroomVsCherryOnICertificate()
    assert cert.check() is True
    assert len(cert.atoms()) == 10          # j=1..5 x {A, B}
    mod = cert.lean_module()
    assert "namespace BGBroomVsCherry" in mod and mod.count("by norm_num") == len(cert.atoms())


def test_leaf_exchange_certificate():
    """LeafExchangeCertificate (extremality leg #5): leaf->cherry strictly raises ell for hub degree d=3..6, so
    bare leaves never occur in the M_d argmax. Pure rational (F* cleared): (3(4d-1)/(2(4d+1)))^11 > 621/64."""
    from telperion.tie_regime import LeafExchangeCertificate
    from fractions import Fraction as Fr
    cert = LeafExchangeCertificate()
    assert cert.check() is True
    assert len(cert.atoms()) == 4           # d=3..6
    for _, lhs, rhs, op in cert.atoms():
        assert op == ">" and lhs > rhs and rhs == Fr(621, 64)
    mod = cert.lean_module()
    assert "namespace BGLeafExchange" in mod and mod.count("by norm_num") == len(cert.atoms())


def test_scl_induction_assembly_certificate():
    """SCLInductionCertificate: the extremality assembly re-checks every arithmetic leg (price-map, broom-vs-cherry,
    leaf-exchange, hi-degree, near-broom, M_d step/tail, mixed-KKT) AND that the price map is closed on I. Gates the
    arithmetic backbone of the single-child induction; the well-founded recursion on |c| remains the open glue."""
    from telperion.tie_regime import SCLInductionCertificate
    cert = SCLInductionCertificate()
    assert cert.check() is True
    # every component leg is itself gated
    comps = cert.components()
    assert len(comps) == 8
    assert all(c.check() for _, c in comps)
    mod = cert.lean_module()
    assert "namespace BGSCLInduction" in mod


def test_per_hub_decouple_residual_certificate():
    """PerHubDecoupleResidualCertificate: the SCL per-hub decouple residual R(S) <= 0 (the highest-risk nlinarith),
    reduced to 20 norm_num atoms via the flowed price mu''=muPP(d,mu) + the upward-parabola-endpoints reduction.
    The single-price step is too loose; the flowed step closes with margin +0.007..+0.076."""
    from telperion.tie_regime import (
        PerHubDecoupleResidualCertificate, _decouple_muPP, _DECOUPLE_SMAX,
    )
    from fractions import Fraction as Fr
    import math
    cert = PerHubDecoupleResidualCertificate()
    assert cert.check() is True
    assert len(cert.atoms()) == 20                                    # d=2..6 x mu in {A,B} x S in {0,Smax}
    # flowed child price stays in I and <= 3/11 for d>=3 (routes leaves safely)
    A, B = Fr(456, 3703), Fr(3, 7)
    for d in range(3, 7):
        assert _decouple_muPP(d, Fr(0)) <= Fr(3, 11)
    # soundness: the true residual R(S) (exact log) is <= 0 at the endpoints (the enclosure only loosens it)
    FSTAR = math.log(621 / 64) / 11
    bVc = lambda mu: (math.log(3 / 2) - 2 * FSTAR) + mu / 3
    def R(d, S, mu):
        s0 = (d - 1) / 3.0; mpp = float(_decouple_muPP(d, mu))
        return ((d - 1) * bVc(mpp) - s0 / (d + s0) + math.log(1 + s0 / d) - FSTAR
                + mu * S / (d + s0) ** 2 + mu / (d + S) - bVc(mu))
    for d in range(2, 7):
        for mu in (float(A), float(B)):
            for S in (0.0, float(_DECOUPLE_SMAX[d])):
                assert R(d, S, mu) <= 1e-9
    mod = cert.lean_module()
    assert "namespace BGPerHubDecouple" in mod and mod.count("by norm_num") == 20
