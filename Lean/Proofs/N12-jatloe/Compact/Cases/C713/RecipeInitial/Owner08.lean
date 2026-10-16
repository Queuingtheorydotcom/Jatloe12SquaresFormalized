import Compact.Cases.C713.RecipeInitial.Data08
import Compact.Cases.C713.SharedDomains

namespace N12Compact.C713RecipeInitial
open S12 S12Pilot DirectPoseCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section


theorem owner8_leaves_shared :
    owner8.leaves = C713Shared.continuousScout713Domain8_0 := by
  unfold owner8
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

#print axioms owner8_leaves_shared

end
end N12Compact.C713RecipeInitial
