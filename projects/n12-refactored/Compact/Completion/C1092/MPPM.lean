import Compact.Completion.C1092.MPPMActualInwardReduction
import Compact.Completion.C1092.MPPMOrdinaryEnding

/-! The original windmill branch. The actual wall-omission, elbow,
inward and ordinary endings keep their original twelve-square owners.
One simultaneous reflection identifies the canonical branch-0 context.
Source only, without compiler or replay acceptance. -/
namespace N12Compact.C1092MPPM
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
set_option Elab.async false

theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : False :=
  C1092MPPMOrdinaryCycle.impossible p hf hb (C1092MPPMActualInward.ordinary p hf hb)

/-- Canonical branch 0 is the opposite orientation of the mppm chart.
Reflection in y=2 transports the complete packing, all closed center
signs and every strict actual-owner point together. -/
theorem windmill : BranchEnding 0 := by
  intro p hf hb
  let g : Transform := ⟨false,false,true⟩
  have action : branchAction g (canonicalBranch 0)=mppm := by
    funext k
    fin_cases k <;> rfl
  have context := context_transport g p hf (canonicalBranch 0) hb
  rw [action] at context
  exact impossible (g.pullPacking p) (family_transport g p hf) context

#print axioms impossible
#print axioms windmill
end N12Compact.C1092MPPM
