import Compact.Cases.C898.RecipeInitial.Data10
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
theorem owner10_leaves_shared :
    owner10.leaves = C898Shared.continuousScout898Domain10_0 := by
  unfold owner10
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

#print axioms owner10_leaves_shared

end N12Compact.C898RecipeInitial
