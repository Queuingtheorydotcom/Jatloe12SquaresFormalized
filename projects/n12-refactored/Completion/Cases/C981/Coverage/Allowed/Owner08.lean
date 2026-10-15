import Completion.Cases.C981.OwnershipDomains

namespace S12Completion.C981.Coverage
open S12
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def allowed8 : List (Finset Nat) := [{0,10},{0,10,13},{1,11},{1,11,13},{0,1,10},{0,1,11},{0,1,10,11},{0,1,10,13},{0,1,11,13},{0,2,10},{1,3,11}]
theorem allowed8_exact : domain8.allowed = allowed8 := by decide +kernel

end S12Completion.C981.Coverage
