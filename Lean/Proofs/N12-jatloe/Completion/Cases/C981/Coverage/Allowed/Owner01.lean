import Completion.Cases.C981.OwnershipDomains

namespace S12Completion.C981.Coverage
open S12
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def allowed1 : List (Finset Nat) := [{0,10},{0,2,10}]
theorem allowed1_exact : domain1.allowed = allowed1 := by decide +kernel

end S12Completion.C981.Coverage
