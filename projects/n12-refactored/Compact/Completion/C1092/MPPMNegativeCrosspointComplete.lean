import Compact.Completion.C1092.MPPMNegativeCrosspointActual
import Compact.Completion.C1092.MPPMNegativeCrosspointCentral
import Compact.Completion.C1092.MPPMNegativeCrosspointG01
import Compact.Completion.C1092.MPPMNegativeCrosspointG10High
import Compact.Completion.C1092.MPPMNegativeCrosspointG11

/-! The retaining-negative crosspoint transfer with every continuous
scalar mode supplied. The upper-half restriction is a conclusion of
the actual geometric sources; no boundary angle is assumed here.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNegativeCrosspointGeometry
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
open C1092MPPMNegativeCrosspointSupport
set_option Elab.async false
noncomputable section

theorem scalar_proof : ScalarProof := by
  intro c s d t cn en steep shallow h r q
  exact ⟨G00_nonnegative cn en steep shallow q,
    fun order => G01_nonnegative c s d t h r cn steep en shallow q order,
    G10_nonnegative c s d t h r cn steep en shallow q,
    fun order => G11_nonnegative c s d t h r cn steep en shallow q order⟩

/-- A positive missing-forward central owner receives its crosspoint
from a retaining nonpositive successor, with genuine actual owners and
all continuous inequalities proved upstream. -/
theorem crosspoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (retaining : (owners p 5).Inside 2 (87/50)) :
    (owners p 4).Inside (3/2) 2 :=
  crosspoint_of_scalars scalar_proof p hf hb h forward C frame cn sp D dframe dn retaining

end
#print axioms scalar_proof
#print axioms crosspoint
end N12Compact.C1092MPPMNegativeCrosspointGeometry
