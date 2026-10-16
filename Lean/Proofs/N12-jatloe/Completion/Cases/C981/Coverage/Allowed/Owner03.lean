import Completion.Cases.C981.OwnershipDomains

namespace S12Completion.C981.Coverage
open S12
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def allowed3 : List (Finset Nat) := [∅,{19},{7},{7,17},{7,19},{9,19}]
theorem allowed3_exact : domain3.allowed = allowed3 := by decide +kernel

end S12Completion.C981.Coverage
