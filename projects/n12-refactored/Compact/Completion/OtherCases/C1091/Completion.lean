import Compact.Completion.OtherCases.C1091.EntranceMixed
import Compact.Completion.OtherCases.C1091.EntranceNorthwest
import Compact.Completion.OtherCases.C1091.RowIdentity

/-! Unconditional original-family source assembly for C1091. The actual
left wall lies strictly above its midpoint. The four closed right/top
sectors are excluded by the reconstructed entrances; no six-point producer
or unavailable historical catalogue is assumed. Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1091.Completion
open S12 S12Completion S12Pilot OriginalData
set_option Elab.async false

theorem family_excluded : ExcludesFamily family := by
  intro p hf
  by_cases right : centerY (owners p 10)≤2
  · by_cases top : centerX (owners p 11)≤2
    · exact EntranceWalls.right_low_top_low_impossible p hf right top
    · exact EntranceNorthwest.impossible p hf right (lt_of_not_ge top).le
  · by_cases top : centerX (owners p 11)≤2
    · exact EntranceMixed.impossible p hf (lt_of_not_ge right).le top
    · exact EntranceAllPositive.impossible p hf (EntranceWalls.left_above p hf).le
        (lt_of_not_ge right).le (lt_of_not_ge top).le

theorem case_excluded : ExcludesCase 1091 := excludes_case family_excluded

#print axioms family_excluded
#print axioms case_excluded
end N12Compact.Completion.OtherCases.C1091.Completion
