import Compact.HistoricalCommon.C973.Step04Data

namespace N12Compact.HistoricalCommon.C973.Step04
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

checked_axis_group group0 (sources,neighbors,positive_denominators,pairKeys,opposite) : 64 × 64 in (0,16,0,16)
checked_axis_group group1 (sources,neighbors,positive_denominators,pairKeys,opposite) : 64 × 64 in (16,8,0,8)
checked_axis_group group2 (sources,neighbors,positive_denominators,pairKeys,opposite) : 64 × 64 in (16,4,8,8)
checked_point_group group3 (sources,neighbors,positive_denominators,ownKeys) : 64 × 64 in (20,4,8,8) at ⟨1916,2095,1000⟩

end
end N12Compact.HistoricalCommon.C973.Step04
