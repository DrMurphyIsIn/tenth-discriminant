# hcn/certificates/

Several of the class number two proof's Lean files are generated: the two radicand sets in the statement, the 1,429
certificates of class number at least three, the bridge data for the eighteen fields of class number two, the range lemma, the
assembly and the main module. They were produced by the scripts in this directory from computed class-number data, and written
into Lean files.

**None of it is trusted.** The kernel re-checks every certificate when the project is built, with `decide +kernel`. A wrong
certificate would make the build fail; it could not make a false theorem. The statement's two sets are a different matter: they
are part of what the theorem says, so they are checked the way the rest of the statement is, by reading them. They are the
classical lists, and Comparator compares the proved statements with them symbol for symbol. The scripts are here so that you can
see where every generated file came from, and confirm that the checked-in files are exactly what the scripts produce.

| Script | Produces |
|---|---|
| `gen_sets.py` | `HCNChallenges/ClassNumberLeTwo.lean`, the two statements with their sets inserted, never typed by hand. It enumerates the fundamental discriminants up to 340,000 from the definition, reads h(−d) from the data below, checks that five class-number sources, from three independent programs, agree on every one of them, and converts the fields with h ≤ 2 to radicands. It also writes the list of the 1,429 radicands with h ≥ 3 and dOf m ≤ 4777, which `gen_certs.py` must reproduce. |
| `gen_certs.py` | `HCN/Finite/Certs.lean` and `Certs/Chunk1.lean` … `Chunk15.lean`: for each of the 1,429 radicands, a certificate of chosen split primes that certifies exactly h ≥ 3. Every hypothesis it emits is checked here twice, by the same search the Lean code runs and by a brute-force search over a box, before it is written. It re-derives the certificates and checks them against an earlier, separate implementation's output (`data/cert_norm_4777.csv`). |
| `gen_classtwo.py` | `HCN/Finite/ClassTwo.lean`: for each of the eighteen fields with h = 2, the bound B, a nonprincipal ramified prime and a positive witness for every other prime below B. |
| `gen_range.py` | `HCN/Assembly/Range.lean` (the range lemma, checked here against the certificate files), `HCN/Assembly.lean`, and `HCN/Main.lean` from the template `Main.lean.in`. The sets are read from the statement file, never typed. |
| `gen_controls.py` | `HCNNegControls/Tamper/*.lean`: the three tampered statements, made from the statement file. |
| `regenerate_and_diff.sh` | Runs all five into `certificates/_regen/` and compares the 24 generated Lean files byte for byte with the files in `../formalization/`. |

The generators are pure Python 3, standard library only, with exact integer arithmetic.

## The data

[`data/`](data) holds the computed class numbers that `gen_sets.py`, `gen_certs.py` and `gen_classtwo.py` read, with the
programs that produced them. We re-ran every program, and each reproduced its file byte for byte.

| File | What it is | Produced by |
|---|---|---|
| `classno_300000_gp.csv.gz` | h(−d) for every fundamental −d with d ≤ 300,000, by PARI's `qfbclassno` | `gp -q gp_classno.gp` (PARI/GP 2.17.4) |
| `classno_300000_forms_dirichlet.csv.gz` | the same range, by counting reduced forms and by Dirichlet's class number formula | `hcn_classno 300000 1` (`hcn_classno.c`) |
| `classno_340000_forms.csv.gz` | d ≤ 340,000, by counting reduced forms | `hcn_classno 340000 0` |
| `classno_340000_independent.csv` | d ≤ 340,000, by a separately written count of reduced forms | `independent_classno 340000` (`independent_classno.c`) |
| `cert_norm_4777.csv` | the chosen primes of each h ≥ 3 certificate, from an earlier, separate implementation, for comparison only | not included |

That is five class-number sources from three independent programs (PARI, `hcn_classno.c` and `independent_classno.c`), and
they agree on every discriminant; `gen_sets.py` also runs a reduced-form count of its own up to d = 5000.

## Checking

```sh
hcn/certificates/regenerate_and_diff.sh
```

This prints one line per check and `ALL OK (24 generated files)`, and removes `_regen/` on success. It takes about five
seconds.

Run before we edited their comments, their paths and the header lines they write, the original generators reproduced all 27
generated files of the checked tree byte for byte (the 24 above, and the three proof-side controls of the run of record, which
are not published). The edits do not touch the arithmetic.

## The generators' own controls

`gen_certs.py --force-controls DIR` and `gen_classtwo.py --force-controls DIR` write certificates that the honest generators
refuse to write, through a forcing adapter, each of which must FAIL to build: claims of h ≥ 3 for d = 8 and d = 15 (class
numbers 1 and 2), a true claim for d = 23 with one hypothesis corrupted or with the ramified prime declared split, and claims of
class number two for m = 431 (class number 21) and m = 23 (class number 3). The honest certificate for d = 23 is written
alongside, as the baseline that must build. `regenerate_and_diff.sh` writes them, under
`_regen/controls/`, but does not build them; to see them fail, copy one into `../formalization/` and run `lake env lean` on it
after building the project.
