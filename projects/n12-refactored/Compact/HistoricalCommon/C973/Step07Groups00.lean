import Compact.HistoricalCommon.C973.Step07Data

namespace N12Compact.HistoricalCommon.C973.Step07
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

checked_axis_group group0 (sources,neighbors,positive_denominators,pairKeys,opposite) : 64 × 64 in (0,8,0,16)
checked_axis_group group1 (sources,neighbors,positive_denominators,pairKeys,opposite) : 64 × 64 in (8,8,0,8)
checked_point_group group2 (sources,neighbors,positive_denominators,ownKeys) : 64 × 64 in (8,8,8,4) at ⟨305,201,100⟩
checked_point_group group3 (sources,neighbors,positive_denominators,ownKeys) : 64 × 64 in (8,8,12,4) at ⟨1553,1020,500⟩

end
end N12Compact.HistoricalCommon.C973.Step07
