import Completion.Cases.C981.Coverage.Data.Allowed05
import Completion.Cases.C981.OwnershipDomains

namespace S12Completion.C981.Coverage
open S12
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem allowed5_exact : domain5.allowed = allowed5 := by decide +kernel

end S12Completion.C981.Coverage
