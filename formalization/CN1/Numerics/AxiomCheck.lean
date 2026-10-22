import CN1.Numerics.Glue

/-!
# Axiom audit for the numerics

Every theorem below must report exactly `propext`, `Classical.choice`, `Quot.sound` (standard axioms
only; no `sorryAx`, no `Lean.ofReduceBool` from `native_decide`).
-/

#print axioms CN1.Numerics.riemannZeta₁_eq_sub_W
#print axioms CN1.Numerics.riemannZeta_eq_of_pos_re
#print axioms CN1.Numerics.riemannZeta_ofReal_eulerMaclaurin
#print axioms CN1.Numerics.riemannZeta_three_quarters
#print axioms CN1.Numerics.riemannZeta_seven_eighths
#print axioms CN1.Numerics.riemannZeta_seven_quarters
#print axioms CN1.Numerics.riemannZeta_three_quarters_re_neg
#print axioms CN1.Numerics.riemannZeta_seven_eighths_re_neg
#print axioms CN1.Numerics.Gamma_ratio_bounds
#print axioms CN1.Numerics.Gamma_ratio_enclosure
#print axioms CN1.Numerics.mainTerm_655_ge
#print axioms CN1.Numerics.B0_655_le
#print axioms CN1.Numerics.mainTerm_sub_B0_pos
#print axioms CN1.Numerics.disc_le_652_of_mainTerm_nonpos
#print axioms CN1.Numerics.CS_mainTerm_sub_B0_pos
#print axioms CN1.Numerics.disc_le_652_of_CS
