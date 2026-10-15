import Compact.HistoricalCommon.C713.Step01Data

namespace N12Compact.HistoricalCommon.C713.Step01
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

checked_axis_group group4 (sources,neighbors,positive_denominators,pairKeys,opposite) : 128 × 128 in (32,16,0,16)
checked_axis_group group5 (sources,neighbors,positive_denominators,pairKeys,opposite) : 128 × 128 in (48,16,0,8)
checked_point_group group6 (sources,neighbors,positive_denominators,ownKeys) : 128 × 128 in (48,16,8,8) at ⟨9895,9767,10000⟩
checked_point_group group7 (sources,neighbors,positive_denominators,ownKeys) : 128 × 128 in (32,32,16,16) at ⟨4702,4783,5000⟩

end
end N12Compact.HistoricalCommon.C713.Step01
