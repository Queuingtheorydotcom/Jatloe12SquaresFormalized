import Completion.Cases.C981.OwnershipDomains

namespace S12Completion.C981.Coverage
open S12
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def allowed4 : List (Finset Nat) := [∅,{11},{1,11},{3},{3,11},{3,14}]
theorem allowed4_exact : domain4.allowed = allowed4 := by decide +kernel

end S12Completion.C981.Coverage
