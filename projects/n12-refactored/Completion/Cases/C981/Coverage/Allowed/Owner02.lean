import Completion.Cases.C981.OwnershipDomains

namespace S12Completion.C981.Coverage
open S12
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def allowed2 : List (Finset Nat) := [∅,{18},{6},{6,15},{6,18},{8,18}]
theorem allowed2_exact : domain2.allowed = allowed2 := by decide +kernel

end S12Completion.C981.Coverage
