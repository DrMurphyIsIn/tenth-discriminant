/- telperion 0.1.6 | family ZeroFree | input-hash aff367d6470249e1
   2 theorems, 1 generation-time self-checks passed.
   Regenerate & verify:  forge diff --family <module:attr> --manifest <manifest.json> --check
   DO NOT EDIT BY HAND — edits are flagged by the regeneration diff.  -/

import Mathlib

namespace G1
namespace ZeroFree

-- zerofree_disk_r2: p = Σ aₖ zᵏ is ZERO-FREE in |z| ≤ 2 by the Rouche
-- dominant-constant-term bound |a₀| > Σ|aₖ|rᵏ; log p is analytic there
-- (Barvinok interpolation / Lee-Yang).  |a₀| = 10, Σ = 6.
theorem zerofree_disk_r2 : ((1/1) * (2/1)^1 + (1/1) * (2/1)^2 : ℚ) < 10/1 := by norm_num

-- zerofree_disk_r3: p = Σ aₖ zᵏ is ZERO-FREE in |z| ≤ 3 by the Rouche
-- dominant-constant-term bound |a₀| > Σ|aₖ|rᵏ; log p is analytic there
-- (Barvinok interpolation / Lee-Yang).  |a₀| = 100, Σ = 54.
theorem zerofree_disk_r3 : ((3/1) * (3/1)^1 + (2/1) * (3/1)^2 + (1/1) * (3/1)^3 : ℚ) < 100/1 := by norm_num

end ZeroFree
end G1
