import Completion.Cases.C981.Coverage.Prefix02

namespace S12Completion.C981.Coverage
open S12 N12Compact.PrefixCoverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def prefix03 : List (List (Finset Nat)) := [
  [{2,12},{0,10},{1,11}],
  [{2,12},{0,10},{1,11,13}],
  [{2,12},{0,10},{1,3,11}]
]
theorem step03 : StepCheck prefix02 allowed8 prefix03 := by
  decide +kernel
end S12Completion.C981.Coverage
