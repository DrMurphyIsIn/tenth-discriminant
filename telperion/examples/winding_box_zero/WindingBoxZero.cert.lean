/- telperion 0.1.6 | family WindingBoxZero | input-hash 1a84c2b7ad83cd5e
   0 theorems, 2 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace WindingBoxZero

/-  winding_zero_inside — WINDING-BOX-ZERO certificate (trust class float-demo, NOT rigorous, NOT kernel).

    Winding-number zero count for the OPEN rectangle
        [0, 1] × [0, 1]:
        winding = 1   (i.e. exactly 1 zero(s) strictly inside).

    Computed by a FLOAT demonstration double (float-demo (node-sampled float phase of z - z0; NOT rigorous)),
    128 boundary samples (32 per side).  This is NOT a rigorous count;
    it exercises the emitter without python-flint.  Re-run at doubled density
    (64 per side) with the same integer.

    TRUST CLASS: float-demo.  This is a SIDECAR record
    (see the .cert.json), documented here the way `campaign.py verify-bands` documents
    turing_band sidecars.  There is NO kernel theorem and NO RH claim.
    conjecture1_proved = False.  -/

/-  winding_zero_outside — WINDING-BOX-ZERO certificate (trust class float-demo, NOT rigorous, NOT kernel).

    Winding-number zero count for the OPEN rectangle
        [1, 2] × [1, 2]:
        winding = 0   (i.e. exactly 0 zero(s) strictly inside).

    Computed by a FLOAT demonstration double (float-demo (node-sampled float phase of z - z0; NOT rigorous)),
    128 boundary samples (32 per side).  This is NOT a rigorous count;
    it exercises the emitter without python-flint.  Re-run at doubled density
    (64 per side) with the same integer.

    TRUST CLASS: float-demo.  This is a SIDECAR record
    (see the .cert.json), documented here the way `campaign.py verify-bands` documents
    turing_band sidecars.  There is NO kernel theorem and NO RH claim.
    conjecture1_proved = False.  -/

end WindingBoxZero
