# SURFACE.md: what the main theorem does not use

Not every declaration in this project is in the dependency closure of `CN1.classNumber_eq_one_iff`. Some are alternative or
supporting statements that were proved along the way, and the vendored files from the first proof bring a good deal that this
proof never touches. None of that matters to the theorem: the kernel checks the closure, and an unused declaration can neither
help nor harm it. But a reader going through the files should know which declarations the proof actually rests on, so this file
lists the rest.

The lists come from the run of record. In an environment that imports every module of `ELEM` and `CN1` (but not the challenge or
a control, see the README's one rule), we walked the closure of `CN1.classNumber_eq_one_iff` (69,295 constants) and listed, module
by module, every user-facing declaration that is not in it. The 215 auxiliary declarations that Lean's compiler generates are not
listed. [`VERIFICATION.md`](VERIFICATION.md) shows that the published modules compile to exactly the same declarations as the
checked ones, so the lists hold for the files here.

## In ELEM

Every `ELEM` module not named below has no unused user-facing declaration.

### Proved, and marked unused in their docstrings

These seven are alternative forms of steps that the final assembly does differently. Each docstring begins "Unused; not in the
closure of `CN1.classNumber_eq_one_iff`."

| Module | Declaration | What it is |
|---|---|---|
| `ELEM.Glue` | `ELEM.dOf_lt_of_classNumber_eq_one` | the analytic bound `dOf m < 2^15` as a theorem of its own; the assembly uses the case split instead |
| `ELEM.Sieve.Range` | `ELEM.Sieve.exists_isWitness_of_dOf_lt` | the finite range stated as "a witness prime exists"; the assembly goes through `ELEM.classNumber_ne_one_of_lt` in `ELEM.Glue` |
| `ELEM.Sieve.Range` | `ELEM.Sieve.not_sieveHit_survivors` | the five survivors really are not rejected (the survivor list is exact) |
| `ELEM.Sieve.Defs` | `ELEM.Sieve.prime_of_mem_sievePrimes` | the sieve primes are prime |
| `ELEM.Sieve.Defs` | `ELEM.Sieve.isWitness_of_sieveHit` | a sieve hit is a witness in the first proof's sense |
| `ELEM.Sieve.Defs` | `ELEM.Sieve.isWitness_two_of_mod_four_ne_three` | `p = 2` ramifies; the closure uses the glue's `ELEM.isWitness_two_of_not_mod_four` |
| `ELEM.Sieve.Defs` | `ELEM.Sieve.isWitness_two_of_mod_eight_eq_seven` | `p = 2` splits; the closure uses the glue's `ELEM.isWitness_two_of_mod_eight` |

### Proved but not used, not marked

| Module | Declaration | What it is |
|---|---|---|
| `ELEM.Defs` | `ELEM.B` | the constant `B = ∑_p (log p)/p²` as a `tsum` |
| `ELEM.Hypotheses` | `ELEM.LemmaTwoTheta`, `ELEM.LemmaTwoB` | the `θ(x)` and `B` parts of Lemma 2, as fixed statements |
| `ELEM.Primes.LemmaTwo` | `ELEM.Primes.lemmaTwoTheta`, `ELEM.Primes.lemmaTwoB` | their proofs |
| `ELEM.Primes.SumLogDivSq` | `ELEM.Primes.summable_log_div_sq`, `ELEM.Primes.tsum_log_div_sq_lt_two_thirds` | the series `B` converges, and `B < 2/3` |
| `ELEM.Primes.Mertens` | `ELEM.Primes.sum_log_div_lt_log_add_of_subset` | the upper bound of `A(m)` for a subset of the primes |
| `ELEM.Endpoint.Comparison` | `ELEM.Endpoint.companion_comparison` | the companion note's form of the endpoint comparison, `846/575 < 143/96`, kept for cross-reference |

**Lemma 2, in particular.** Of the three estimates in Lemma 2, only the one for `A(m)` (`ELEM.LemmaTwoA`, proved by
`ELEM.Primes.lemmaTwoA`) is used by the main theorem. The `θ(x)` and `B` parts are proved, exactly as stated, but the final
theorem does not use them. The divisibility step needs the same two bounds only for finite sets of primes, and takes them from the
finite-set lemmas `ELEM.Primes.sum_log_lt_three_halves_mul` and `ELEM.Primes.sum_log_div_sq_lt_two_thirds`, which are in the
closure.

### Used, although they leave no constant in the closure

The listing also names `ELEM.redHom_re` and `ELEM.redHom_im` in `ELEM.Frobenius`. They are **not** unused. They are `@[simp]`
lemmas proved by `rfl`, saying what reduction modulo `p` does to the two coordinates, and `simp` uses them while elaborating
`ELEM.redHom_node_injective` in `ELEM.Nonvanishing.Params`, which is in the closure. Because they hold by definition, `simp`
applies them by unfolding, and the finished proof term does not mention them. So they leave no constant in the closure, but the
proof as written needs them.

## In the vendored CN1 files

The vendored modules are byte-identical copies of the first proof's files, and much of them serves the first proof only: its
Kronecker character, its 190 witnesses and its ramification lemmas. They were not edited, so that they stay identical.

| Module | In the closure | Unused |
|---|---|---|
| `CN1.Finite.Bridge` | 9 | 1: `classNumber_ne_one_of_foundations` |
| `CN1.Finite.Converse` | 11 | 0 |
| `CN1.Finite.Elementary` | 6 | 0 |
| `CN1.Finite.Params` | 10 | 1: `le_dOf` |
| `CN1.Finite.SplitPrime` | 14 | 3: `SqfBelow`, `sqfBelow_of_squarefree`, and the generated `NumberField.classNumber.congr_simp` |
| `CN1.Finite.Witnesses` | 0 | 5: `classNumber_ne_one_of_quadInt`, `exists_witness_of_mem`, `nonHeegner190`, `mem_nonHeegner190`, `length_nonHeegner190` |
| `CN1.Finite.Witnesses.Chunk1` … `Chunk4` | 0 | 52, 52, 52 and 42: the first proof's witness instances `w_…`, with `chunkN` and `exists_witness_chunkN` |
| `CN1.Foundations.Basic` | 47 | 12 |
| `CN1.Foundations.Character` | 0 | 39: the whole Kronecker-character development |
| `CN1.Foundations.Discr` | 7 | 1: the generated `intBasis.congr_simp` |
| `CN1.Foundations.Ramified` | 0 | 10: the whole module, which `ELEM.Main` does not even import |
| `CN1.Foundations.Splitting` | 6 | 25 |

The `congr_simp` entries are congruence lemmas that Lean generates for `simp`, not declarations written in the source. The first
proof's witness files are imported (through `CN1.Finite.Bridge`) but contribute nothing to the closure: this proof settles the
finite range with the residue sieve instead.
