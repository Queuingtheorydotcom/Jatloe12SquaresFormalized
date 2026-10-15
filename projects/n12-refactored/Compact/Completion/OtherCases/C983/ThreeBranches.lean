import Compact.Completion.OtherCases.C983.F5LowerRight
import Compact.Completion.OtherCases.C983.InwardAlternative

/-! Complete original C983 merged-owner entrance to the three remaining
continuous endings. Every prior reduction retains actual point ownership. -/
namespace N12Compact.Completion.OtherCases.C983
open S12
set_option Elab.async false
noncomputable section

def mergedFinalComponents : List (Finset Nat) :=
  [{4,13},{5,13},{4,5,13}]

private theorem merged_three_check :
    ∀ owned∈mergedInitialComponents,14∉owned → (4∈owned ∨ 5∈owned) →
      owned∈mergedFinalComponents := by decide +kernel

theorem merged_three_branches (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    actual p 7∈mergedFinalComponents :=
  merged_three_check _ (merged_initial_components p hf)
    (merged_no_g4 p hf) (merged_inward_alternative p hf)

end
#print axioms merged_three_branches
end N12Compact.Completion.OtherCases.C983

