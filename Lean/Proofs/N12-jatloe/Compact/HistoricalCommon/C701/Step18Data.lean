import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings005
import Compact.HistoricalCommon.Bindings006
import Compact.HistoricalCommon.Bindings023
import Compact.HistoricalCommon.Bindings024
import Compact.HistoricalCommon.Bindings025
import Compact.HistoricalCommon.Bindings026
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step18
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 64 → Context dictionary :=
  ![context754,context765,context786,context807,context822,context833,context838,context839,context840,context841,context755,context756,context757,context758,context759,context760,context761,context762,context763,context764,context767,context769,context771,context773,context775,context777,context779,context781,context783,context785,context788,context790,context792,context794,context796,context798,context800,context802,context804,context806,context809,context811,context813,context815,context816,context817,context818,context819,context820,context821,context823,context824,context825,context826,context827,context828,context829,context830,context831,context832,context834,context835,context836,context837]

def neighbors : Fin 45 → Context dictionary :=
  ![context171,context172,context173,context174,context175,context176,context177,context178,context179,context180,context181,context182,context183,context184,context185,context186,context187,context188,context189,context190,context191,context192,context193,context194,context195,context196,context197,context198,context199,context200,context201,context202,context203,context204,context205,context206,context207,context208,context209,context210,context211,context212,context213,context214,context215]


end
end N12Compact.HistoricalCommon.C701.Step18
