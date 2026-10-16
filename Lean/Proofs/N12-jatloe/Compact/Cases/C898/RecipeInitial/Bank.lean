import Compact.Bridge.DirectRecipeDictionary
import Compact.Cases.C898.SharedDictionary
import Compact.Cases.C898.DirectInitial.Inputs

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false


noncomputable def bank : DirectRecipeTable.Bank 64 C898Shared.poseCount :=
  DirectRecipeTable.Bank.ofDictionary C898Shared.dictionary C898Shared.positive_denominators

theorem bank_pose (i : Fin C898Shared.poseCount) : bank.poses i = C898Shared.poses i :=
  C898Shared.dictionary_pose i

end N12Compact.C898RecipeInitial
