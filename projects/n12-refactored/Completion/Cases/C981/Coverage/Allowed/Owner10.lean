import Completion.Cases.C981.OwnershipDomains

namespace S12Completion.C981.Coverage
open S12
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def allowed10 : List (Finset Nat) := [{8,18},{8,16,18},{9,19},{9,16,19},{6,8,18},{7,9,19},{8,9,18},{8,9,19},{8,9,16,18},{8,9,16,19},{8,9,18,19}]
theorem allowed10_exact : domain10.allowed = allowed10 := by decide +kernel

end S12Completion.C981.Coverage
