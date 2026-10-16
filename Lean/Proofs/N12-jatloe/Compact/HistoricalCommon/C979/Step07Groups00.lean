import Compact.HistoricalCommon.C979.Step07Data

namespace N12Compact.HistoricalCommon.C979.Step07
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

checked_axis_group group0 (sources,neighbors,positive_denominators,pairKeys,opposite) : 128 × 128 in (0,16,0,16)
checked_axis_group group1 (sources,neighbors,positive_denominators,pairKeys,opposite) : 128 × 128 in (16,16,0,8)
checked_point_group group2 (sources,neighbors,positive_denominators,ownKeys) : 128 × 128 in (16,16,8,8) at ⟨1071,1023,1000⟩
checked_axis_group group3 (sources,neighbors,positive_denominators,pairKeys,opposite) : 128 × 128 in (32,32,0,8)

end
end N12Compact.HistoricalCommon.C979.Step07
