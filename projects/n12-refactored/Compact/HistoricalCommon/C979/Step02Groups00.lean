import Compact.HistoricalCommon.C979.Step02Data

namespace N12Compact.HistoricalCommon.C979.Step02
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

checked_axis_group group0 (sources,neighbors,positive_denominators,pairKeys,opposite) : 128 × 128 in (0,32,0,8)
checked_axis_group group1 (sources,neighbors,positive_denominators,pairKeys,opposite) : 128 × 128 in (32,32,0,4)
checked_point_group group2 (sources,neighbors,positive_denominators,ownKeys) : 128 × 128 in (32,32,4,4) at ⟨3143,2599,1000⟩
checked_point_group group3 (sources,neighbors,positive_denominators,ownKeys) : 128 × 128 in (0,64,8,8) at ⟨619,526,200⟩

end
end N12Compact.HistoricalCommon.C979.Step02
