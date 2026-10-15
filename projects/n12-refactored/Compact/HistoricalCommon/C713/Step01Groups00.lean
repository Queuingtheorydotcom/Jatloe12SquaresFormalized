import Compact.HistoricalCommon.C713.Step01Data

namespace N12Compact.HistoricalCommon.C713.Step01
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

checked_axis_group group0 (sources,neighbors,positive_denominators,pairKeys,opposite) : 128 × 128 in (0,16,0,16)
checked_axis_group group1 (sources,neighbors,positive_denominators,pairKeys,opposite) : 128 × 128 in (0,8,16,16)
checked_point_group group2 (sources,neighbors,positive_denominators,ownKeys) : 128 × 128 in (8,8,16,16) at ⟨541,500,500⟩
checked_axis_group group3 (sources,neighbors,positive_denominators,pairKeys,opposite) : 128 × 128 in (16,16,0,32)

end
end N12Compact.HistoricalCommon.C713.Step01
