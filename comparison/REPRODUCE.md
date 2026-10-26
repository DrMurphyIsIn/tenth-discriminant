# Reproducing the claims

**NOT kernel-checked.** Everything here is a computation in Arb ball arithmetic (python-flint), with outward rounding, plus a
few clearly marked numerical (floating-point) checks. Each command below prints what it proves, and the expected output is in
[`results/`](results/).

**Requirements.** Python 3.9 or later, `python-flint` (we used 0.6.0) and `mpmath` (we used 1.3.0):

```sh
pip install python-flint==0.6.0 mpmath==1.3.0
```

Run the commands from this directory (`comparison/`). Pin BLAS threads to one, because nothing here gains from them:

```sh
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
```

## The theorem: h = 1 implies |D| < 565

**1. The four bands [565, 652]**, from our band data in `data/`. This takes about 30 seconds.

```sh
python3 code/own_cert_all.py
```

The command prints one line per band. Each line gives the certified gap at Q₀ (it must be > 0), the worst upper bound for U′
over eight Taylor cells (it must be < −γ = −0.2341), and the exact monotonicity criterion. The last line must be
`ALL FOUR BANDS CERTIFIED: True`. Expected output: [`results/own_cert_all.out`](results/own_cert_all.out), md5
`02b85c93aefc3e9dc2ff0b2600e0f6a2`.

| Band | gap at Q₀ | U′ (worst cell) |
|---|---|---|
| [565, 570] | 0.00227502121066 | −2.256 ± 0.0009 |
| [570, 580] | 0.0200891981736 | −2.35 ± 0.002 |
| [580, 600] | 0.0558097548413 | −2.39 ± 0.002 |
| [600, 652] | 0.124424072587 | −2.43 ± 0.005 |

`own_cert_all.py` also takes another directory of band files as its only argument. That lets you certify data that you made
yourself (step 2).

**2. (Optional) Make the band data again from nothing.** This step chooses the rows: the minimal κ for each, certified by the
sieve inequality. It also chooses γ, and the kernel by the generalised eigenproblem. It writes `own_<Q0>_<Q1>.json` into the
current directory, so run it somewhere else:

```sh
mkdir -p /tmp/regen && cd /tmp/regen
for b in "565 570" "570 580" "580 600" "600 652"; do python3 <path to comparison>/code/own_params.py $b; done
```

(In zsh, write `${=b}` for `$b`.) Each band takes about five minutes. The files it writes are byte-for-byte equal to the
ones in `data/`; we checked this from a clean directory. Only the choice of data depends on this
search. The certificate in step 1 checks whatever data it is given.

**3. Above 652.** Here we rely on the first entry's kernel-checked theorem d ≤ 652; see [`../formalization/`](../formalization/).

**4. Below 565: the finite range.** This counts reduced forms for all 173 fundamental discriminants with 3 ≤ q < 565:

```sh
python3 code/finite_below_565.py
```

It must find h = 1 exactly at q = 3, 4, 7, 8, 11, 19, 43, 67 and 163. Expected output:
[`results/finite_below_565.out`](results/finite_below_565.out).

## The reproduction of v0.6.1 (optional; needs twinheterodox's repository)

twinheterodox's repository has no licence, so we do not ship any of it. Check it out at commit 44c7d6fc and run:

```sh
python3 code/repro_v61.py <path to twinheterodox/tenth-discriminant>/versions/v6.1
```

The script asserts the md5 of `parameters.json`, and that its t, C, τ and γ equal the constants written into
`code/assemble.py`. It then computes the band [570, 580] in v0.6.1's own configuration: Mertens constant 1.334, and the closed
form (29) for K(j). The output is `10.9754131603100 ± 1.2e-14`, against v0.6.1's 10.975413160309. Expected output:
[`results/repro_v61.out`](results/repro_v61.out).

## The survey's reproduced rows and the strength scale

Each of these runs in seconds:

| Command | What it shows | Expected output |
|---|---|---|
| `python3 survey/cs_validate.py` | our Chowla–Selberg normalisation, against direct lattice sums (numerical) | [`cs_validate.out`](results/survey/cs_validate.out) |
| `python3 survey/rcs_edge.py` | the edge form: 7/8 gives d ≤ 653, so d ≤ 652, since −653 is not a discriminant; 11/12 gives d ≤ 1151 | [`rcs_edge.out`](results/survey/rcs_edge.out) |
| `python3 survey/rcs_grh.py` | GRH, conditional: d ≤ 199, with the limit 64π²e^(−2γ) = 199.1208… | [`rcs_grh.out`](results/survey/rcs_grh.out) |
| `python3 survey/rcs_zero.py` | zero forcing, 1 − β < κ/√d: Banks gives d < 10¹⁰; Kimura Thm 1 | [`rcs_zero.out`](results/survey/rcs_zero.out) |
| `python3 survey/rcs_curve.py` | the σ₀ family as one curve, and the inverse σ_D | [`rcs_curve.out`](results/survey/rcs_curve.out) |
| `python3 survey/rcs_flip.py` | the strength scale σ_eq(D₀) for every row; q < 570 is worth 0.861 | [`rcs_flip.out`](results/survey/rcs_flip.out) |
| `python3 survey/rcs_kimura_grid.py <Kimura's cln-imq-2k-1.4>` | Kimura's grid: d < 6.47·10⁷ (chain 58) and d < 1.23·10⁸ (chain 59); needs Kimura's repository | [`rcs_kimura_grid.out`](results/survey/rcs_kimura_grid.out) |
| `python3 survey/cs_complex_zeros.py` | exploratory, numerical, not a claim: does the main term have complex zeros? | [`cs_complex_zeros.out`](results/survey/cs_complex_zeros.out) |

Part (2) of `rcs_flip.py` is a heuristic extrapolation of v0.6.1's band margins, and it is not a claim. It runs only if you
pass v0.6.1's directory as an argument; the expected output above includes it.

## Checking the files

Every file in this directory is listed with its md5 in [`MANIFEST.md5`](MANIFEST.md5):

```sh
md5sum -c MANIFEST.md5          # Linux
```

On macOS, compare against `md5 -r` instead.
