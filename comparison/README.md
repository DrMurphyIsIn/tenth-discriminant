**NOT kernel-checked.** Certified by interval arithmetic (Arb), and reproduced per band by a separately written AI
implementation (high-precision floating point). Inputs:
- Rosser–Schoenfeld 1962 (Table I; Theorems 4, 6, 9, 14; (3.21) for the Mertens correction, cited), for [565, 652];
- Rosser–Schoenfeld 1962 (2.11), the constant E (all nine bands);
- the modern explicit bounds for θ(x) of Broadbent–Kadiri–Lumley–Ng–Wilk (arXiv:2002.11068v2) and Büthe (Math. Comp. 87, 2018),
  read at source, double-transcribed and tested against exact prime sums to 10⁹, for [548, 565];
- OpenAI's 7/8 theorem, which enters only through the first entry's kernel-checked bound d ≤ 652, for q ≥ 653.

# Tenth-discriminant bounds compared

This directory is the fourth entry in this repository, and unlike the other three it is not a Lean proof. It answers the
question Tao's challenge actually asks: if a tenth imaginary quadratic field of class number one existed, how large could its
discriminant be, according to each of the arguments posted in the thread? The thread now holds about twenty such extractions,
made with different reductions and different standards of proof. Here they are side by side, and then one of them, the
strongest light-machinery bound, is rebuilt from scratch and pushed a little further.

There are three parts.

1. **A survey.** Every posted extraction, quoted at source with its author and comment number, in one table, and labelled by
   what we could check: **R**, reproduced independently by us; **R\***, a kernel-checked formalisation, not a recomputation; **C**, cited as posted, not yet checked by us;
   **NR**, not reproducible from what was posted. Every input that can be written as "no real zero in (σ₀, 1)" goes through one
   reduction, the Chowla–Selberg expansion of the principal form, so that the rows compare methods and not reductions. Read
   backwards, the same curve puts every method on one scale: the zero-free abscissa it is "worth" on this problem. On that
   scale twinheterodox's light determinant bound q < 570 is worth 0.861, which is ahead of the 7/8 half-plane.
2. **A reproduction** of that bound, twinheterodox v0.6.1 (after Green, van Dijk, Pratt and Kerr), from our own derivation and
   our own code. In v0.6.1's own configuration the lower bound of its band [570, 580] comes out as 10.9754131603100, against
   its 10.975413160309, and the per-row envelope coefficients agree to within 6.3·10⁻¹⁴.
3. **An improvement**, to an analytic cutoff (new in v1.4.0: 548, down from 565):

   > If h(ℚ(√D)) = 1 for a fundamental discriminant D < 0, then |D| < 548.

   Four certified bands exclude [565, 652] with the 1962 prime estimates. Five more exclude [548, 565] with modern explicit
   bounds for the Chebyshev function θ(x), which shrink the intervals in which the method must find an auxiliary inert prime. The
   first entry's kernel-checked theorem d ≤ 652 excludes everything above. A direct count of reduced forms checks the
   fundamental discriminants below 548, and it finds exactly the nine. The improvement over 570 is about 3.9%, and it changes no
   candidate discriminant. What it measures is the method's strength, and that is what the challenge compares.

The paper, [`paper/paper.pdf`](paper/paper.pdf) (10 pages), has the survey table, the derivation in outline, the controls, and
the limits.

## What the result is, and what it is not

The theorem lives in the class "unconditional, Heegner-free, with a quasi-Riemann input". Between 565 and 652 the argument is the
determinant method alone, with Rosser–Schoenfeld's explicit prime estimates. Above 652 it is the first entry's theorem, which uses
OpenAI's 7/8 half-plane. Since a light-machinery bound is also valid in that class, the comparison with 570 is made inside it.

It is fragile, and we would rather say so than have someone find out:

- **The margin is small.** The binding band [548, 550] has margin 0.0013, against a Poisson-mode error allowance of 0.0016. There
  the prime inputs are saturated (a 1% change moves the gap by about 5·10⁻⁸, a 1% change in one row's κ by 6·10⁻⁶); what
  binds is the sieve and the kernel. 547, the
  next candidate prime, is not reached.
- **A correction to v1.3.0.** v1.3.0 used Rosser–Schoenfeld's 17-digit approximation of Mertens' constant E with a ball of radius
  10⁻¹⁷, which misses the true E by 1.8·10⁻¹⁸. v1.4.0 uses their correctly rounded 15-digit value with radius 10⁻¹⁵. The ball's
  midpoint moves by 1.3·10⁻¹⁶, so every gap moves by about 10⁻¹⁶; no conclusion changes, and all nine bands are re-certified.
- **One improvement carries the result.** It is the exact treatment of the Poisson modes in the norm series. With
  contour-shift error accounting instead, the band [565, 570] fails by 41.6.
- **Going lower failed.** Our attempts on [560, 565], [562, 565] and [563, 565] did not certify.

**Why it is not kernel-checked.** The argument needs explicit prime estimates of Rosser–Schoenfeld quality at scales up to about
10¹⁶. The explicit-bounds files of PrimeNumberTheoremAnd (at commit c39a7511) state such results but rest them on trusted
numerical inputs or `sorry`. So nothing of that quality is three-axiom-clean in Lean yet. A kernel-checked version is future
work. Until then, these are computations certified in ball arithmetic and checked by a second, independent implementation.
Both implementations are AI-written, and no human has checked either.

## Credits

- **The determinant method and the bound 570** are twinheterodox's (github.com/twinheterodox/tenth-discriminant, commit
  44c7d6fc, version v0.6.1), with the credits given there to Green, van Dijk, Pratt and Kerr. That repository has no licence.
  So nothing of it is copied here: we re-derived each step, and our code reads its parameters only in the optional reproduction
  script, from a path you supply.
- **The zero-forcing route** is twinheterodox's and michaelmross's.
- **The thread's other values:** the evaluation at the edge, and the 11/12 value 1151, are LemmaLab's. The Kimura extraction
  route is Rudolph's. The inert-prime facts are classical, as Silberman and Pratt emphasised.
- **Kimura's zero-gap theorems** are formalised in Lean by Kimura. We read his statements, and we did not replay his Lean.
- **The explicit bounds for θ(x)** used for [548, 565] are those of S. Broadbent, H. Kadiri, A. Lumley, N. Ng and K. Wilk, and of
  J. Büthe. D. Platt and T. Trudgian first showed θ(x) < x up to 1.39·10¹⁷. Checking them against exact prime sums, we found two
  printed statements in the arXiv versions that do not hold as printed, and we use corrected forms: Büthe's (1.6) fails on
  [1423, 1427), and one Table 13 entry of Broadbent et al. is too small. Büthe's lies below the scales used here; the Table 13 entry lies within them, and we exclude it and use the
  other entries of that row. The paper gives the details.
- **Our contributions** are the survey and its verification, the strength scale, the reproduction, and the improvements:
  - the Poisson modes;
  - the sharper Rosser–Schoenfeld constant;
  - our own rows, γ and kernels;
  - the Taylor-model band check;
  - a certified K(1/9);
  - the modern explicit prime inputs (v1.4.0).

The work was carried out with Claude (Anthropic) in Claude Code. The derivations, code and text were AI-generated. Every result
was reviewed by a separate AI session, which wrote its own implementation. These are AI reviews, not human peer review. The author
directed the work and takes responsibility for the claims.

## What is here

| Path | What it is |
|---|---|
| [`paper/`](paper/) | `paper.pdf`, its source `paper.tex` and `refs.bib` |
| [`code/`](code/) | the certificate code for the theorem (Arb via python-flint, outward rounding throughout) |
| [`data/`](data/) | our band data `own_<Q0>_<Q1>.json` (1962 inputs) and `modern_<Q0>_<Q1>.json` (modern inputs); Rosser–Schoenfeld's Table I, `rs_table_I.json`; the modern θ bounds as transcribed, `transcription_theta_bounds.json` |
| [`controls/`](controls/) | the truth test of the θ bounds against exact prime sums (`c9_truth.py`), the class-number-one truth sandwich (`c1a_modern.py`) and the degradation test (`c3_degrade.py`) |
| [`results/`](results/) | the outputs the commands in REPRODUCE.md should give you |
| [`survey/`](survey/) | the scripts behind the survey's R rows and the strength scale |
| [`REPRODUCE.md`](REPRODUCE.md) | one command per claim |
| [`MANIFEST.md5`](MANIFEST.md5) | md5 of every file in this directory |

In `code/`:

- `primes.py`: the prime-sum bounds from Rosser–Schoenfeld.
- `sieve.py`: the auxiliary-prime rows.
- `assemble.py`: the per-row constants, the eight stages, and the envelope L(x).
- `outer.py`: the kernel average, and the upper bound with the Poisson modes.
- `band81.py`: the band-uniformity check.
- `kj_cert.py`: the certified K(j).
- `x2_kernel.py`: the kernel search and the gap certificate.
- `own_params.py`: makes our band data.
- `own_cert_all.py`: certifies the four 1962 bands [565, 652].
- `cert_modern.py`: certifies the five modern bands [548, 565].
- `modern_profile.py`: the modern explicit bounds for θ(x), assembled from the transcription.
- `finite_below_565.py`: the finite check below 565.
- `repro_v61.py`: the optional reproduction of v0.6.1.

Comments in the code of the form "bb X" or "lead" refer to items in our internal review log, which is not published. "bb" is the
independent AI review session, and "lead" is the session that wrote the code. We kept the comments so that each fix stays tied to
the reason for it.

Three scripts read files that we do not ship, and each takes the path as an argument:

- `code/repro_v61.py` reads v0.6.1's `parameters.json`. It pins the file's md5, and it refuses to run without the path.
- `survey/rcs_kimura_grid.py` reads Kimura's Lean grid and his `B4Certificates.lean`. It pins both md5s, and it refuses to run
  without the path.
- Part (2) of `survey/rcs_flip.py`, a heuristic extrapolation of v0.6.1's band margins, reads v0.6.1's certificate files.
  Without the path, it skips that part.
