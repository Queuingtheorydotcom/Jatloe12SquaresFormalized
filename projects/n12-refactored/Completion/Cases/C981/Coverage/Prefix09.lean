import Completion.Cases.C981.Coverage.Data.Prefix09
import Completion.Cases.C981.Coverage.Prefix08

namespace S12Completion.C981.Coverage
open S12 N12Compact.PrefixCoverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem step09 : StepCheck prefix08 allowed4 prefix09 := by
  decide +kernel
end S12Completion.C981.Coverage
