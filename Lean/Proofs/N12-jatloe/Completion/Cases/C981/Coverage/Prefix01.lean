import Completion.Cases.C981.Coverage.Prefix00

namespace S12Completion.C981.Coverage
open S12 N12Compact.PrefixCoverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def prefix01 : List (List (Finset Nat)) := [
  [{2,12}],
  [{2,10,12}]
]
theorem step01 : StepCheck prefix00 allowed0 prefix01 := by
  decide +kernel
end S12Completion.C981.Coverage
