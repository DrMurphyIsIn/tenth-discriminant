# computations/

Independent numerical checks of step 4 of the argument (see the top-level README). These are evidence and a guide for the Lean
proof, not part of it.

- `cs_threshold.py`: mpmath at 50 digits. It evaluates the Chowla–Selberg expression for ζ_K(7/8) (principal form, a = 1) for every
  admissible d ≤ 3000. It reports the largest d at which the value is ≤ 0 (it is d = 652) and the values near the threshold. A sanity
  check compares with direct lattice sums at s = 2.
- `arb_threshold.py`: Arb ball arithmetic via python-flint at 256 bits. It certifies ζ(3/4) < 0 and ζ(7/8) < 0,
  M(652) = −0.0022412 < 0 and M(655) = +0.0011379 > 0, and that the main term increases in d. It bounds the Bessel remainder with a
  standard K-Bessel inequality that is **not proved here**, and truncates that series at n < 60. The Lean version will replace both
  with a proved bound.

A correction, recorded here for transparency: an earlier draft of these scripts used the prefactor 2^{s+1/2} for the Bessel series
in place of the correct 2^{s+3/2}. An independent review caught it by testing against lattice sums at small d, where the Bessel term
is visible. At the threshold (d ≈ 655) the term is about 10⁻³⁵, so the conclusion did not change.

Requirements: `pip install mpmath python-flint`.
