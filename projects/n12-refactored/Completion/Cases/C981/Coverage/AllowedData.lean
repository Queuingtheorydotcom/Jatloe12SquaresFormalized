import Completion.Cases.C981.Coverage.Allowed.Owner00
import Completion.Cases.C981.Coverage.Allowed.Owner01
import Completion.Cases.C981.Coverage.Allowed.Owner02
import Completion.Cases.C981.Coverage.Allowed.Owner03
import Completion.Cases.C981.Coverage.Allowed.Owner04
import Completion.Cases.C981.Coverage.Allowed.Owner05
import Completion.Cases.C981.Coverage.Allowed.Owner06
import Completion.Cases.C981.Coverage.Allowed.Owner07
import Completion.Cases.C981.Coverage.Allowed.Owner08
import Completion.Cases.C981.Coverage.Allowed.Owner09
import Completion.Cases.C981.Coverage.Allowed.Owner10
import Completion.Cases.C981.Coverage.Allowed.Owner11
import Compact.Bridge.CoverageReorder

namespace S12Completion.C981.Coverage
open S12 N12Compact.PrefixCoverage
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def literalChoices : List (List (Finset Nat)) :=
  [allowed0,allowed1,allowed2,allowed3,allowed4,allowed5,allowed6,allowed7,allowed8,allowed9,allowed10,allowed11]
theorem allowed_exact : domains.map (fun d => d.allowed) = literalChoices := by
  simp only [domains,List.map_cons,List.map_nil,allowed0_exact,allowed1_exact,allowed2_exact,allowed3_exact,allowed4_exact,allowed5_exact,allowed6_exact,allowed7_exact,allowed8_exact,allowed9_exact,allowed10_exact,allowed11_exact]
  rfl

def reorderedChoices : List (List (Finset Nat)) :=
  [allowed0,allowed1,allowed8,allowed9,allowed10,allowed11,allowed2,allowed3,allowed4,allowed5,allowed6,allowed7]
theorem reordered_exact : reorder literalChoices = reorderedChoices := rfl
end S12Completion.C981.Coverage
