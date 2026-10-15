import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings008
import Compact.HistoricalCommon.Bindings009
import Compact.HistoricalCommon.Bindings010
import Compact.HistoricalCommon.Bindings016
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step13
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 39 → Context dictionary :=
  ![context281,context283,context285,context541,context542,context526,context537,context538,context292,context294,context296,context298,context300,context302,context539,context540,context306,context308,context310,context312,context314,context316,context318,context320,context322,context324,context326,context328,context330,context332,context334,context336,context338,context340,context342,context344,context346,context348,context350]

def neighbors : Fin 10 → Context dictionary :=
  ![context527,context528,context529,context530,context531,context532,context533,context534,context535,context536]


end
end N12Compact.HistoricalCommon.C701.Step13
