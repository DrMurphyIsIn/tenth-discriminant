"""Density-decay exponent -- the thermodynamic-diffusion characterization of the approach to D_inf.

As a self-similar tree family grows (orbitals fill), the per-vertex density D(s)=Phi^11^(1/n) relaxes to
its asymptote D_inf.  The FUNCTIONAL FORM of the excess delta(s)=D(s)-D_inf distinguishes two physical
regimes (operator's diffusion analogy):

  * power-law (Fickian, standard/ordered media):     delta ~ c * s^(-alpha),  peak density ~ t^(-d/2)
  * stretched-exponential (disordered/fractal media): delta ~ exp(-c s^beta)

MEASURED: the ordered legs-2 / legs-3 / path families all decay as a CLEAN POWER LAW with alpha ~ 1
(R^2 ~ 0.999+), i.e. effective dimension d ~ 2 -- the STANDARD diffusion branch, not the stretched-
exponential branch (which is reserved for disordered media).  alpha=1 is structural, not fitted:
ln D(s) - ln D_inf = C/(2s+1) + O(1/s^2), the correction being a single hub vertex plus a half-integer
shift, both O(1/s).  So D(s) is linear in 1/s and approaches D_inf monotonically FROM ABOVE.

BOTH functional forms are first-class skills here: power_law_fit (Fickian/ordered) and
stretched_exponential_fit (disordered/fractal), plus classify_decay_regime which runs both and reports
which the family obeys.  This is a DESCRIPTIVE physical characterization (an ordered structure => clean
power-law relaxation), not a proof lever: the tail bound D_inf < 1 is the integer inequality in
fractal_eigenvalue.py, independent of the decay form.  A family found to decay as a STRETCHED exponential
would flag a disordered regime worth a counterexample hunt -- but the ordered extremal families are all
Fickian.  conjecture1_proved = False.
"""
from __future__ import annotations

import math

from .rooted_phi import bg_phi11_fast


def _density(n, edges):
    return float(bg_phi11_fast(n, edges)) ** (1.0 / n)


def near_star_family(s):
    e = []
    nid = 1
    for _ in range(s):
        p = 0
        for _ in range(2):
            e.append((p, nid)); p = nid; nid += 1
    return 2 * s + 1, tuple(e)


def spider_family(s, leg=3):
    e = []
    nid = 1
    for _ in range(s):
        p = 0
        for _ in range(leg):
            e.append((p, nid)); p = nid; nid += 1
    return 1 + leg * s, tuple(e)


def path_family(s):
    k = 2 * s + 1
    return k, tuple((i, i + 1) for i in range(k - 1))


def _richardson_dinf(sizes, dens):
    """Estimate D_inf assuming delta ~ c/s, from the two largest sizes."""
    s1, s2 = sizes[-2], sizes[-1]
    d1, d2 = dens[-2], dens[-1]
    return (s2 * d2 - s1 * d1) / (s2 - s1)


def density_decay_fit(family_fn, sizes):
    """Fit delta(s)=D(s)-D_inf ~ s^(-alpha) for a growing family (family_fn(s)->(n,edges)).
    Returns dict(D_inf, alpha, eff_dim=2*alpha, r2, regime).  alpha~1 & high r2 => Fickian/ordered."""
    dens = [_density(*family_fn(s)) for s in sizes]
    d_inf = _richardson_dinf(sizes, dens)
    xs = [math.log(s) for s in sizes[:-1]]
    ys = [math.log(abs(_density(*family_fn(s)) - d_inf)) for s in sizes[:-1]]
    m = len(xs)
    mx = sum(xs) / m
    my = sum(ys) / m
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    yhat = [my + slope * (x - mx) for x in xs]
    ss_res = sum((y - yh) ** 2 for y, yh in zip(ys, yhat))
    ss_tot = sum((y - my) ** 2 for y in ys)
    r2 = 1 - ss_res / ss_tot if ss_tot else 0.0
    alpha = -slope
    regime = "Fickian/ordered (power-law)" if r2 > 0.99 and 0.7 < alpha < 1.3 else "anomalous/other"
    return {"D_inf": d_inf, "alpha": alpha, "eff_dim": 2 * alpha, "r2": r2, "regime": regime}


def power_law_fit(family_fn, sizes):
    """Alias: fit delta(s) ~ s^(-alpha) (the Fickian/ordered form).  Same as density_decay_fit."""
    return density_decay_fit(family_fn, sizes)


def stretched_exponential_fit(family_fn, sizes, beta_grid=None):
    """Fit delta(s)=D(s)-D_inf ~ A*exp(-c s^beta) (the disordered/fractal form).  Sweeps beta, picking
    the exponent whose ln(delta)-vs-s^beta regression is most linear.  Returns dict(D_inf, c, beta, r2)."""
    if beta_grid is None:
        beta_grid = [round(0.1 * k, 2) for k in range(2, 21)]     # 0.2 .. 2.0
    dens = [_density(*family_fn(s)) for s in sizes]
    d_inf = _richardson_dinf(sizes, dens)
    ys = [math.log(abs(_density(*family_fn(s)) - d_inf)) for s in sizes[:-1]]
    ss = sizes[:-1]
    m = len(ss)
    best = None
    for beta in beta_grid:
        xs = [s ** beta for s in ss]
        mx = sum(xs) / m
        my = sum(ys) / m
        denom = sum((x - mx) ** 2 for x in xs)
        if denom == 0:
            continue
        slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / denom
        yhat = [my + slope * (x - mx) for x in xs]
        ss_res = sum((y - yh) ** 2 for y, yh in zip(ys, yhat))
        ss_tot = sum((y - my) ** 2 for y in ys)
        r2 = 1 - ss_res / ss_tot if ss_tot else 0.0
        if best is None or r2 > best["r2"]:
            best = {"D_inf": d_inf, "c": -slope, "beta": beta, "r2": r2}
    return best


def classify_decay_regime(family_fn, sizes):
    """Run BOTH fits and report which functional form the family's relaxation obeys.  Returns
    dict(regime, power_law, stretched_exp, verdict).  For ordered self-similar tree families this is
    Fickian; a stretched-exponential winner would flag a disordered regime (a counterexample-hunt cue)."""
    pl = power_law_fit(family_fn, sizes)
    se = stretched_exponential_fit(family_fn, sizes)
    # power-law is the alpha=1, beta=1 special case of stretched-exp; prefer it unless SE is clearly better
    stretched_wins = se["r2"] > pl["r2"] + 0.01 and not (0.85 <= se["beta"] <= 1.15)
    return {
        "regime": "stretched-exponential (disordered)" if stretched_wins else "power-law (Fickian/ordered)",
        "power_law": pl,
        "stretched_exp": se,
        "verdict": ("disordered/fractal media -- worth a counterexample hunt" if stretched_wins
                    else f"ordered media, eff_dim d~{pl['eff_dim']:.2f}"),
    }


def laplace_surface_tension(family_fn, sizes):
    """Balloon/Laplace reading of the 1/s density term: D(s) = D_inf + c/s, with c the effective
    SURFACE TENSION (the coefficient of the surface free-energy term ~ surface/volume ~ 1/n).  Laplace's
    law DeltaP = 2*gamma/r <=> delta(s)=c/s.  Returns dict(D_inf_bulk, tension=c, from_above=c>0,
    r2, uniform).  c>0 => density approached FROM ABOVE (the 'inflated balloon').  `uniform` flags whether
    the LOCAL tension c(s)=s(s+1)(D(s)-D(s+1)) is ~constant (a uniform membrane) or drifts (sub-leading
    curvature corrections -- nonlinear wall).  DESCRIPTIVE physics, not a proof lever: it re-expresses the
    measured 1/s relaxation as a surface-tension term.  conjecture1_proved=False."""
    d_inf, c, r2 = is_linear_in_inverse_s(family_fn, sizes)
    locals_ = []
    for s in (sizes[0], sizes[len(sizes) // 2], sizes[-1]):
        d0 = _density(*family_fn(s))
        d1 = _density(*family_fn(s + 1))
        locals_.append(s * (s + 1) * (d0 - d1))
    spread = max(locals_) - min(locals_)
    return {"D_inf_bulk": d_inf, "tension": c, "from_above": c > 0, "r2": r2,
            "local_tensions": locals_, "uniform": spread < 0.05 * abs(c) if c else False}


def default_family_zoo():
    """Ordered..disordered growing tree families for scouting.  Disordered ones (RRT, pref-attach) are
    seeded/incremental so each is a well-defined growing structure."""
    import random

    def comb(s):
        e = [(i, i + 1) for i in range(s - 1)] + [(i, s + i) for i in range(s)]
        return 2 * s, tuple(e)

    def caterpillar2(s):
        e = [(i, i + 1) for i in range(s - 1)]; nid = s
        for i in range(s):
            e += [(i, nid), (i, nid + 1)]; nid += 2
        return 3 * s, tuple(e)

    def rrt(s):
        rng = random.Random(20260817)
        return s, tuple((rng.randint(0, v - 1), v) for v in range(1, s))

    def prefattach(s):
        rng = random.Random(20260817); tg = [0]; e = []
        for v in range(1, s):
            p = rng.choice(tg); e.append((p, v)); tg += [p, v]
        return s, tuple(e)

    return {
        "near-star(L2)": near_star_family, "path": path_family,
        "legs-3": lambda s: spider_family(s, 3), "legs-5": lambda s: spider_family(s, 5),
        "comb": comb, "caterpillar-2": caterpillar2,
        "RRT(uniform)": rrt, "pref-attach": prefattach,
    }


def scout_disorder(families=None, sizes=(40, 80, 160, 320)):
    """Scout a family space for STRETCHED-EXPONENTIAL (disordered) density decay -- the regime where an
    anomaly could hide.  Returns {name: classify_decay_regime(...)} plus a 'flagged' list of disordered
    families.  Ordered/Fickian families are the extremal ones; a flagged family is a counterexample-hunt
    cue (but only a THREAT if its density is also high -- check separately)."""
    fams = families if families is not None else default_family_zoo()
    out = {}
    flagged = []
    for name, fn in fams.items():
        try:
            r = classify_decay_regime(fn, list(sizes))
            out[name] = r
            if "stretched" in r["regime"]:
                flagged.append(name)
        except Exception as ex:  # pragma: no cover
            out[name] = {"error": str(ex)}
    out["_flagged_disordered"] = flagged
    return out


def is_linear_in_inverse_s(family_fn, sizes):
    """Direct alpha=1 test: is D(s) linear in 1/s?  Returns (D_inf_intercept, slope_c, r2)."""
    dens = [_density(*family_fn(s)) for s in sizes]
    xs = [1.0 / s for s in sizes]
    m = len(xs)
    mx = sum(xs) / m
    my = sum(dens) / m
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, dens)) / sum((x - mx) ** 2 for x in xs)
    icept = my - slope * mx
    yhat = [icept + slope * x for x in xs]
    r2 = 1 - sum((y - yh) ** 2 for y, yh in zip(dens, yhat)) / sum((y - my) ** 2 for y in dens)
    return icept, slope, r2
