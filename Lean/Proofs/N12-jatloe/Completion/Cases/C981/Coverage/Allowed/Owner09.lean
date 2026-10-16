import Completion.Cases.C981.OwnershipDomains

namespace S12Completion.C981.Coverage
open S12
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def allowed9 : List (Finset Nat) := [{2,12},{2,10,12},{2,12,15},{6,15},{6,12,15},{6,15,18},{2,4,12},{2,4,12,15},{2,6,12,15},{4,6,15},{4,6,12,15}]
theorem allowed9_exact : domain9.allowed = allowed9 := by decide +kernel

end S12Completion.C981.Coverage
