-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Main

/-!
# Axioms of the main theorems

Prints the axioms on which each main theorem depends.
-/

#print axioms Rectiling.soundness
#print axioms Rectiling.completeness
#print axioms Rectiling.completeness_square
#print axioms Rectiling.solve_sound
#print axioms Rectiling.solve_complete
#print axioms Rectiling.solve_spec
#print axioms Rectiling.Primitives.ideal
#print axioms Rectiling.reported_sound
#print axioms Rectiling.reported_complete
#print axioms Rectiling.reported_iff
