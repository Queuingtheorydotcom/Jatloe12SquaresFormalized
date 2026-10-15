import Compact.Cases.C898.RecipeInitial.Data06
import Compact.Cases.C898.SharedDomains

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false


/-- Equality to the complete original reduced domain, including empty roots. -/
theorem owner6_leaves_shared :
    owner6.leaves = C898Shared.continuousScout898Domain6_0 := by
  unfold owner6
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

#print axioms owner6_leaves_shared

end N12Compact.C898RecipeInitial
