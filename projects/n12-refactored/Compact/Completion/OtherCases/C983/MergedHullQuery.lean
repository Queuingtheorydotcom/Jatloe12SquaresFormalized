import Compact.Bridge.SharedLocalQueries

/-! The exact mixed hull that the larger C983 F/G allowances require.
The anchors are the actual southwest marker,F3,G6 of the merged owner.
No joint-vector catalogue or continuous geometry hypothesis is added. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false

checked_local_query mergedF3G6 := ⟨2304,2,{3,16},
  .hull ⟨(33/20,33/20),(8/5,3),(113/50,2),(2,113/50),624/845,503/841⟩⟩

end N12Compact.Completion.OtherCases.C983

