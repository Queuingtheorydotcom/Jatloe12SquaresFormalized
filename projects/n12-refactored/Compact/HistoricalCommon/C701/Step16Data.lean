import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings016
import Compact.HistoricalCommon.Bindings019
import Compact.HistoricalCommon.Bindings020
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step16
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 47 → Context dictionary :=
  ![context618,context629,context638,context646,context656,context660,context661,context662,context663,context664,context619,context620,context621,context622,context623,context624,context625,context626,context627,context628,context630,context631,context632,context633,context634,context635,context636,context637,context639,context640,context641,context642,context643,context644,context645,context647,context648,context649,context650,context651,context652,context653,context654,context655,context657,context658,context659]

def neighbors : Fin 10 → Context dictionary :=
  ![context527,context528,context529,context530,context531,context532,context533,context534,context535,context536]


end
end N12Compact.HistoricalCommon.C701.Step16
