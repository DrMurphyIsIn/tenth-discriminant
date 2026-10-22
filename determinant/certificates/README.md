# determinant/certificates/

The determinant proof has one piece of generated input: the residue sieve that settles the finite range below 2^15. Every integer
q ≡ 3 (mod 8) with 8 < q < 2^15 (there are 4,095 of them, squarefree or not) is either one of 11, 19, 43, 67, 163, or has a prime
p ∈ {3, 5, …, 31} with 4p < q at which X² − X + (q + 1)/4 has a root modulo p. Such a prime is not inert, so the field of
discriminant −q cannot have class number one. The other residue classes are handled in Lean by two short lemmas about the prime 2,
with no enumeration at all.

The statement is checked by the Lean kernel, with `decide +kernel`, in eight files of 512 values of k each
(`determinant/formalization/ELEM/Sieve/Chunk0.lean` … `Chunk7.lean`, with q = 8k + 3). **Nothing the generator does is trusted.**
A wrong list in a chunk file would make the Lean build fail; it could not make a false theorem. The generator is here so that you
can see where the chunk files came from, and confirm that the checked-in files are exactly what it produces.

| Script | Produces |
|---|---|
| `gen_sieve.py` | The eight chunk files, and two negative controls. It also recomputes, independently, how many candidates each prime rejects first, checks its root test against a direct test of whether −q is a square mod p, and checks that each control fails exactly where it should. It exits non-zero if any count disagrees with the record. |
| `regenerate_and_diff.sh` | Runs `gen_sieve.py` into `certificates/_regen/` and compares the eight chunk files byte for byte with the checked-in ones. |

The generator is pure Python 3, standard library only, with exact integer arithmetic.

## Checking

```sh
determinant/certificates/regenerate_and_diff.sh
```

This prints one line per check and `ALL OK`, and removes `_regen/` on success. It takes well under a second.

## The two controls

A checker that accepts everything is worthless, so the generator also writes two chunk files that must **fail**. They are not
checked in; `gen_sieve.py <dir>` writes them to `<dir>/controls/`.

- `Control_No31_Chunk7.lean` is chunk 7 with 31 removed from the prime list. The claim is still true, but q = 32323 is the one
  candidate whose only rejecting prime is 31, so the kernel must reject the file.
- `Control_167_Chunk0.lean` is chunk 0 with 163 replaced by 167 in the survivor list. Then q = 163 is neither listed nor rejected,
  so again the kernel must reject the file.

To see them fail, copy one into `determinant/formalization/` and run `lake env lean Control_No31_Chunk7.lean` there after building
the project; Lean reports a kernel error (`application type mismatch`). In the run of record both were rejected this way, and a
diagnostic check confirmed that each fails at exactly the predicted value of k (k = 4040 and k = 20) and nowhere else.

## About this copy of the generator

The generator is the one that produced the checked chunk files, with a handful of edits that do not touch the computation: the
docstring and one comment no longer name internal plans, the header line written into each chunk file names this path, the controls are
written under the output directory rather than next to the script, and the label of one control was shortened. Run before
those edits, the original generator reproduces the checked chunk files byte for byte; run after them, this copy reproduces the
published chunk files byte for byte. The two sets of chunk files differ only in that header line.
