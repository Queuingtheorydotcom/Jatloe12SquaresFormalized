import Compact.Bridge.DirectRecipeDictionary
import Compact.Cases.C713.SharedDictionary
import Compact.Cases.C713.RecipeInitial.Inputs

namespace N12Compact.C713RecipeInitial
open S12 S12Pilot DirectPoseCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section


def bank : DirectRecipeTable.Bank 192 HistoricalData.poseCount :=
  DirectRecipeTable.Bank.ofDictionary C713Shared.dictionary HistoricalData.positive_denominators

theorem bank_pose (i : Fin HistoricalData.poseCount) : bank.poses i = C713Shared.poses i := rfl

end
end N12Compact.C713RecipeInitial
