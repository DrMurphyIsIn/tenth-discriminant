# certificates/

Some of the Lean proof's inputs are data: the 190 split-prime witnesses for the finite range, the exact rational brackets for the
1000-term zeta sums, and the integer brackets behind the Γ-ratio and the threshold at d = 655. That data was produced by the scripts
in this directory and written into Lean files. **None of it is trusted.** The kernel re-checks every fact when the project is built,
with `decide +kernel` and `norm_num`. A wrong number in a script would make the Lean build fail; it could not make a false theorem.

These scripts are here so that you can see where the data came from, and confirm that the checked-in Lean files are exactly what
the scripts produce.

| Script | Produces |
|---|---|
| `witnesses.py` | `witnesses.json`: for each of the 197 fundamental discriminants −d with 4 < d ≤ 652, the least prime p < (d + 1)/4 that splits (or none). It also computes the class number in two independent ways (reduced forms, and Dirichlet's formula) and checks that a witness exists exactly when h(−d) > 1. The seven discriminants with no witness are 7, 8, 11, 19, 43, 67 and 163. |
| `gen_witnesses.py` | `formalization/CN1/Finite/Witnesses.lean` and `Witnesses/Chunk1.lean` … `Chunk4.lean`: one kernel-checked witness for each of the 190 non-Heegner radicands m. |
| `gen_zeta_tables.py` | `formalization/CN1/Numerics/ZetaTables.lean`: the rational brackets for the Euler–Maclaurin sums at s = 3/4, 7/8 and 7/4. |
| `gen_gamma_numbers.py` | the integer brackets quoted in `formalization/CN1/Numerics/GammaRatio.lean` (the Bohr–Mollerup enclosure of Γ(3/8)/Γ(7/8), with n = 8000). |
| `gen_threshold_numbers.py` | the brackets quoted in `formalization/CN1/Numerics/Threshold.lean` (2^(3/4), 655^(−3/8) and √π), and the resulting lower bound for M(655). |

The generators use exact integer and rational arithmetic only; no floating-point value reaches Lean. They need only Python 3
(`witnesses.py` uses sympy for a second opinion on primality, if it is installed).

## Checking

```sh
certificates/regenerate_and_diff.sh
```

This regenerates everything into `certificates/_regen/` and checks four things:
- the witness rows agree with `witnesses.json`;
- the five witness files and `ZetaTables.lean` are byte-for-byte identical to the files in `formalization/`;
- the integer brackets quoted in `ZetaValues.lean`, `GammaRatio.lean` and `Threshold.lean` are exactly what the generators print;
- the generators' own key inequalities hold.

It prints `ALL OK` and removes `_regen/` on success. It takes about a second.

For an independent numerical view of the threshold, in mpmath and in Arb ball arithmetic, see
[`../computations/`](../computations/README.md).
