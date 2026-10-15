import Compact.Completion.C1092.MPPMMissingNegativeCrosspointActual
import Compact.Completion.C1092.MPPMMissingNegativeCrosspointCentral
import Compact.Completion.C1092.MPPMMissingNegativeCrosspointG01
import Compact.Completion.C1092.MPPMMissingNegativeCrosspointG10
import Compact.Completion.C1092.MPPMMissingNegativeCrosspointG11

/-! The missing-negative transfer with the four complete continuous
scalar bounds. The fixed epsilon is the actual positive-face allowance;
all boundary angles and weak support contacts remain included.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointGeometry
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
open C1092MPPMMissingNegativeCrosspointSupport
set_option Elab.async false
noncomputable section

theorem scalar_proof : ScalarProof := by
  intro c s d t cn en steep large h r q
  refine ⟨?_,?_,?_,?_⟩
  · exact le_trans (by norm_num) (G00star_lower cn en steep large q (le_refl (43/500)))
  · exact le_trans (by norm_num)
      (G01star_lower (43/500) c s d t h r cn steep en large q (le_refl _))
  · exact le_trans (by norm_num)
      (G10star_lower (43/500) c s d t h r cn steep en large q (le_refl _))
  · exact le_trans (by norm_num)
      (G11star_lower (43/500) c s d t h r cn steep en large q (le_refl _))

/-- A missing nonpositive successor forces the positive predecessor's
actual crosspoint without a crosspoint premise on that successor. -/
theorem crosspoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (nextMissing : ¬(owners p 5).Inside 2 (87/50)) :
    (owners p 4).Inside (3/2) 2 :=
  crosspoint_of_scalars scalar_proof p hf hb h forward C frame cn sp D dframe dn nextMissing

end
#print axioms scalar_proof
#print axioms crosspoint
end N12Compact.C1092MPPMMissingNegativeCrosspointGeometry
