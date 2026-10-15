import Compact.Cases.C713.RecipeInitial.Data01
import Compact.Cases.C713.SharedDomains

namespace N12Compact.C713RecipeInitial
open S12 S12Pilot DirectPoseCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section


theorem owner1_leaves_shared :
    owner1.leaves = C713Shared.continuousScout713Domain1_0 := by
  unfold owner1
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

#print axioms owner1_leaves_shared

end
end N12Compact.C713RecipeInitial
