import Compact.Completion.C1092.MPPMActualPositiveCycle
import Compact.Completion.C1092.MPPMCrosspointCentralAll
import Compact.Completion.C1092.MPPMCrosspointBoundaryG01
import Compact.Completion.C1092.MPPMCrosspointBoundaryG10
import Compact.Completion.C1092.MPPMCrosspointBoundaryG11

/-! Unconditional scalar assembly and the complete actual all-positive
ordinary MPPM ending. Every forward-membership pattern is included.
Only the authentic Ordinary entrance and the canonical positive frames
are hypotheses of the sector theorem; all point/face/order producers
and all continuous scalar proofs have source bodies. Source only. -/
namespace N12Compact.C1092MPPMActualPositiveCycle
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MPPMActualPositiveOrder C1092MPPMCrosspointSupport
set_option Elab.async false
noncomputable section

theorem scalar_proof : ScalarProof := by
  intro c s d t cn en steep h r q
  refine ⟨?_,G01_nonnegative c s d t h r cn steep en q,?_,
    G11_nonnegative c s d t h r cn steep en q⟩
  · have lower := Central.g00_lower cn en steep q
    linarith only [lower]
  · apply G10_nonnegative c s d t h r cn steep en q
    intro a b normal lower
    have bound := Central.aligned_C normal en lower
    linarith only [bound]

theorem all_crosspoints (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (positive : PositiveFrames p) :
    AllCrosspoints p := all_crosspoints_of_scalars scalar_proof p hf hb h positive

/-- The complete all-positive ordinary sector. This does not replace
the remaining genuine ordinary/inward and mixed-sign entrance producers. -/
theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (positive : PositiveFrames p) : False :=
  impossible_of_scalars scalar_proof p hf hb h positive

end
#print axioms scalar_proof
#print axioms all_crosspoints
#print axioms impossible
end N12Compact.C1092MPPMActualPositiveCycle
