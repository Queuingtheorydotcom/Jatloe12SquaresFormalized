import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings016
import Compact.HistoricalCommon.Bindings028
import Compact.HistoricalCommon.Bindings029
import Compact.HistoricalCommon.Bindings030
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step21
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 45 → Context dictionary :=
  ![context921,context932,context943,context954,context960,context961,context962,context963,context964,context965,context922,context923,context924,context925,context926,context927,context928,context929,context930,context931,context933,context934,context935,context936,context937,context938,context939,context940,context941,context942,context944,context945,context946,context947,context948,context949,context950,context951,context952,context953,context955,context956,context957,context958,context959]

def neighbors : Fin 10 → Context dictionary :=
  ![context527,context528,context529,context530,context531,context532,context533,context534,context535,context536]


end
end N12Compact.HistoricalCommon.C701.Step21
