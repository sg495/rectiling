-- SPDX-License-Identifier: LGPL-3.0-or-later
import Rectiling.Main
import Rectiling.Search
import Rectiling.Exact
import Rectiling.Target
import Rectiling.Persistence
import Rectiling.ProportionBound
import Rectiling.TilingCount
import Rectiling.CombinatorialMap

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

#print axioms Rectiling.Fast.Run.trace
#print axioms Rectiling.Fast.Elims.det_eq
#print axioms Rectiling.Fast.Run.final_eq_det
#print axioms Rectiling.Fast.Run.final_vanishes
#print axioms Rectiling.Fast.Run.solution
#print axioms Rectiling.Fast.Run.final_eq_target
#print axioms Rectiling.Fast.Elims.pivot_eq_det
#print axioms Rectiling.Fast.division_exact
#print axioms Rectiling.Fast.check_accept
#print axioms Rectiling.Fast.check_reject
#print axioms Rectiling.Fast.dvd_iff_evalAt_eq_zero
#print axioms Rectiling.Fast.Numerics.ideal
#print axioms Rectiling.Fast.leaf_spec
#print axioms Rectiling.Fast.direct_spec
#print axioms Rectiling.Fast.fastSolve_sound
#print axioms Rectiling.Fast.fastSolve_complete
#print axioms Rectiling.Fast.solve_subset_fastSolve
#print axioms Rectiling.Fast.fastSolve_eq_solve
#print axioms Rectiling.mem_completions
#print axioms Rectiling.mem_completions_iff_prefix
#print axioms Rectiling.mem_forcedCompletions
#print axioms Rectiling.flatMap_forcedCompletions
#print axioms Rectiling.nodup_completions
#print axioms Rectiling.Fast.searched_iff
#print axioms Rectiling.Fast.exploreForced_iff_examined
#print axioms Rectiling.Fast.examinedForced_eq
#print axioms Rectiling.Fast.examined_split
#print axioms Rectiling.Fast.examined_once
#print axioms Rectiling.Fast.examined_complete
#print axioms Rectiling.Fast.fast_sound
#print axioms Rectiling.Fast.fast_complete
#print axioms Rectiling.Fast.fast_iff
#print axioms Rectiling.Fast.reported_imp_fast
#print axioms Rectiling.Fast.fast_iff_reported
#print axioms Rectiling.IsTiling.refine
#print axioms Rectiling.Rect.isTiling_pinwheel
#print axioms Rectiling.TilesWith.add_three
#print axioms Rectiling.TilesWith.add_five
#print axioms Rectiling.Achievable.add_four
#print axioms Rectiling.achievable_one
#print axioms Rectiling.persistence
#print axioms Rectiling.persistence_of_one_lt

#print axioms Rectiling.Network.Proper.exists_isFlow
#print axioms Rectiling.Network.IsFlow.unique
#print axioms Rectiling.Network.IsFlow.impedance_eq
#print axioms Rectiling.Network.Proper.impedance_pos
#print axioms Rectiling.Network.Proper.pairPoly_ne_zero
#print axioms Rectiling.Network.natDegree_pairPoly_le
#print axioms Rectiling.Network.IsFlow.aeval_pairPoly
#print axioms Rectiling.IsTiling.sum_bottom_eq_sum_top
#print axioms Rectiling.IsTiling.heightNetwork_isFlow
#print axioms Rectiling.IsTiling.heightNetwork_proper
#print axioms Rectiling.IsTiling.impedance_heightNetwork
#print axioms Rectiling.IsSimilarTiling.aeval_pairPoly
#print axioms Rectiling.Network.Iso.pairPoly_eq
#print axioms Rectiling.Achievable.exists_class
#print axioms Rectiling.finite_achievable
#print axioms Rectiling.ncard_achievable_le
#print axioms Rectiling.IsSimilarTiling.eq_of_heightPair_eq
#print axioms Rectiling.finite_similarTilings
#print axioms Rectiling.finite_similarTilingSets
#print axioms Rectiling.tutteM_le
#print axioms Rectiling.limsup_le_of_le_tutteM
#print axioms Rectiling.TutteEnumeration.card_eq_tutteM
