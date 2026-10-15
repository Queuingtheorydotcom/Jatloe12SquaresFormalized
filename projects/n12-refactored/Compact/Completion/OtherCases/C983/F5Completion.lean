import Compact.Completion.OtherCases.C983.F5ThreeSquareEntrance
import Compact.Completion.OtherCases.C983.NegativeTripleEnd

/-! The F5 branch of original case C983, using its actual-owner entrance
and the shared physical three-square ending. The separate F4 branch is
not addressed by this declaration. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false

theorem f5_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f5 : 5∈actual p 7) : False := by
  obtain ⟨E,N,R,input,_,_,_⟩ := f5_pairwise_three_square_entrance p hf f5
  exact NegativeTripleEnd.impossible E N R input.toInput input.apartEN

#print axioms f5_impossible
end N12Compact.Completion.OtherCases.C983
