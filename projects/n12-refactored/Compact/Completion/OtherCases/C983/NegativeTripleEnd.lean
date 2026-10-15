import Compact.Completion.OtherCases.C983.NegativeForeignFaces
import Compact.Completion.OtherCases.C983.NegativeMixedRight
import Compact.Completion.OtherCases.C983.NegativeMixedSouth

/-! The shared physical three-square ending. The entrance must supply
the genuine disjointness of the two central owners in addition to the
original right-triple input. The four exact face combinations are exhaustive. -/
namespace N12Compact.Completion.OtherCases.C983.NegativeTripleEnd
open S12 S12Pilot
set_option Elab.async false

theorem impossible (E N R : OpenSquare) (input : RightTripleData.Input E N R)
    (apartEN : ∀ x y,¬(E.Inside x y ∧ N.Inside x y)) : False := by
  have sideN : 1<N.side := by
    simpa only [←input.sameEN] using input.southeastFaces.sideLarge
  have sameNR : N.side=R.side := input.sameEN.symm.trans input.sameER
  have north := NegativeTripleNorthSeparation.separators N R sideN sameNR
    input.northeastFaces input.rightFaces input.northeastSharp input.northeastTop input.apartNR
  have south := NegativeRightSeparation.separators E R (-E.s) input.sameER
    input.southeastFaces input.rightFaces input.southeastElbow input.apartER
  rcases south with south | south
  · rcases north with north | north
    · exact NegativeForeignFaces.impossible E N R input apartEN north south
    · exact NegativeMixedSouth.impossible E N R input north south
  · rcases north with north | north
    · exact NegativeMixedRight.impossible E N R input north south
    · exact NegativeRightOwned.impossible E N R input north south

#print axioms impossible
end N12Compact.Completion.OtherCases.C983.NegativeTripleEnd
