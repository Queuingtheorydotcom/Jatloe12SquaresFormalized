import Completion.Cases.C981.Coverage.Prefix03

namespace S12Completion.C981.Coverage
open S12 N12Compact.PrefixCoverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def prefix04 : List (List (Finset Nat)) := [
  [{2,12},{0,10},{1,11},{6,15}],
  [{2,12},{0,10},{1,11},{6,15,18}],
  [{2,12},{0,10},{1,11},{4,6,15}],
  [{2,12},{0,10},{1,11,13},{6,15}],
  [{2,12},{0,10},{1,11,13},{6,15,18}],
  [{2,12},{0,10},{1,11,13},{4,6,15}],
  [{2,12},{0,10},{1,3,11},{6,15}],
  [{2,12},{0,10},{1,3,11},{6,15,18}],
  [{2,12},{0,10},{1,3,11},{4,6,15}]
]
theorem step04 : StepCheck prefix03 allowed9 prefix04 := by
  decide +kernel
end S12Completion.C981.Coverage
