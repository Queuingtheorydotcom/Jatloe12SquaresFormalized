import Completion.Cases.C981.Coverage.Data.Prefix10
import Completion.Cases.C981.Coverage.Prefix09

namespace S12Completion.C981.Coverage
open S12 N12Compact.PrefixCoverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem step10 : StepCheck prefix09 allowed5 prefix10 := by
  apply stepCheck_of_extensions_eq
  rfl
end S12Completion.C981.Coverage
