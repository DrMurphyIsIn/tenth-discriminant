/- telperion 0.1.6 | family WindingBoxZero | input-hash 1a84c2b7ad83cd5e
   0 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace WindingBoxZero

/-  winding_zero_inside — WINDING-BOX-ZERO certificate (Arb-trust-class, NOT kernel).

    Rigorous winding-number zero count for the OPEN rectangle
        [0, 1] × [0, 1]:
        winding = 1   (i.e. exactly 1 zero(s) strictly inside).

    Computed by the argument principle: 128 rational boundary samples
    (32 per side) at working precision 64, each evaluated in an Arb
    ball; the signed quadrant advance / 4 is the winding integer.  A sign-ambiguous or
    diagonal-jump node ABORTS (refine), so the integer is rigorous.  RE-VERIFIED at doubled
    precision (128) and doubled density (64 per side) —
    both runs reproduce the same integer.

    TRUST CLASS: arb (interval arithmetic).  This is a SIDECAR fact
    (see the .cert.json), documented here the way `campaign.py verify-bands` documents
    turing_band sidecars.  There is NO kernel theorem and NO RH claim.
    conjecture1_proved = False.  -/

/-  winding_zero_outside — WINDING-BOX-ZERO certificate (Arb-trust-class, NOT kernel).

    Rigorous winding-number zero count for the OPEN rectangle
        [1, 2] × [1, 2]:
        winding = 0   (i.e. exactly 0 zero(s) strictly inside).

    Computed by the argument principle: 128 rational boundary samples
    (32 per side) at working precision 64, each evaluated in an Arb
    ball; the signed quadrant advance / 4 is the winding integer.  A sign-ambiguous or
    diagonal-jump node ABORTS (refine), so the integer is rigorous.  RE-VERIFIED at doubled
    precision (128) and doubled density (64 per side) —
    both runs reproduce the same integer.

    TRUST CLASS: arb (interval arithmetic).  This is a SIDECAR fact
    (see the .cert.json), documented here the way `campaign.py verify-bands` documents
    turing_band sidecars.  There is NO kernel theorem and NO RH claim.
    conjecture1_proved = False.  -/

end WindingBoxZero
