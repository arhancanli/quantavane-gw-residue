module

import Solution

/-!
# Axiom check

`lake env lean scripts/CheckAxioms.lean` (after `lake build`) prints the axioms that each compared
theorem of `Solution.lean` depends on. Palomar permits only `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms GwResidue.theorem1
#print axioms GwResidue.exists_goodExactColouring
#print axioms GwResidue.lt_of_gwProperty
#print axioms GwResidue.lt_GW
#print axioms GwResidue.gw_r4_l4
#print axioms GwResidue.gw_r5_l4
