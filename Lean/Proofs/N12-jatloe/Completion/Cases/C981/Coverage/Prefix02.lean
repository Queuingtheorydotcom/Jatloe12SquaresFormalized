import Completion.Cases.C981.Coverage.Prefix01

namespace S12Completion.C981.Coverage
open S12 N12Compact.PrefixCoverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def prefix02 : List (List (Finset Nat)) := [
  [{2,12},{0,10}]
]
theorem step02 : StepCheck prefix01 allowed1 prefix02 := by
  decide +kernel
end S12Completion.C981.Coverage
