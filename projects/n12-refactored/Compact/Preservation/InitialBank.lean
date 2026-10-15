import Compact.Bridge.DirectRecipeDictionary
import Compact.Cases.C713.SharedDictionary

namespace N12Compact.Preservation.InitialBank
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section


def bank : DirectRecipeTable.Bank 192 HistoricalData.poseCount :=
  DirectRecipeTable.Bank.ofDictionary C713Shared.dictionary HistoricalData.positive_denominators

theorem angles64_cover_kernel : CoversInterval 0 1 (angles64.map Subtype.val) := by
  decide +kernel

theorem angles128_cover_kernel : CoversInterval 0 1 (angles128.map Subtype.val) :=
  C713Shared.angles128_cover_kernel

end
end N12Compact.Preservation.InitialBank
