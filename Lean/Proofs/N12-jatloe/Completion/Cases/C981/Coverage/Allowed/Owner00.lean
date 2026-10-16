import Completion.Cases.C981.OwnershipDomains

namespace S12Completion.C981.Coverage
open S12
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def allowed0 : List (Finset Nat) := [{2,12},{2,10,12}]
theorem allowed0_exact : domain0.allowed = allowed0 := by decide +kernel

end S12Completion.C981.Coverage
