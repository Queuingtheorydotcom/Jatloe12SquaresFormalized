import Compact.Bridge.C696WallCycle
import Completion.Cases.C696.CornerReduction

/-! Retained source adapter for the two original corner roots. Its original
stronger corner dependencies are separately recorded as missing; this file
is not an accepted or import-closed build root. The unconditional wall-point
theorem itself does not depend on those stronger corner lemmas. -/
namespace N12Compact.C696WallCycle
open S12 S12Pilot S12Completion.C696 SideSignPacking CornerReduction

/-- Both original corner roots still need a coupled contradiction. -/
theorem excludes_case_of_wall_progress
    (finish : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
      ∀ r : Fin 2, ResidualContext p r →
      (∀ i : Fin 4, 21/10 < centerY (wallFrame p i) ∧
        (wallFrame p i).Inside 1 (64/25)) → False) :
    S12Completion.ExcludesCase 696 := by
  apply excludes_case_of_residuals
  intro p hf r hr
  exact finish p hf r hr (frame_progress p hf)

#print axioms excludes_case_of_wall_progress
end N12Compact.C696WallCycle
