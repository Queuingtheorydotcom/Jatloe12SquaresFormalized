import Compact.Completion.C1092.MPPMActualInwardPoints
import Compact.Completion.C1092.MPPMActualNonordinary

/-! Whole-packing opposite-sector transport used by the inward case
split. The two labels below are literal actual point pairs, with no
disjointness or exclusive-label convention built into their definitions. -/
namespace N12Compact.C1092MPPMActualInward
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover
set_option Elab.async false
noncomputable section

def halfTurn : Transform := ⟨false,true,true⟩

def NorthOrdinary (p : NormalizedPacking) : Prop :=
  (owners p 6).Inside 3 (113/50) ∧ (owners p 6).Inside 3 (12/5)

def NorthInward (p : NormalizedPacking) : Prop :=
  (owners p 6).Inside 2 (113/50) ∧ (owners p 6).Inside (113/50) 2

theorem half_context (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : WallContext (halfTurn.pullPacking p) mppm := by
  have action : branchAction halfTurn mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport halfTurn p hf mppm hb
  rwa [action] at context

theorem half_inside (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (x y : ℝ) :
    (owners (halfTurn.pullPacking p) i).Inside x y ↔
      (owners p (ownerAction halfTurn i)).Inside (4-x) (4-y) := by
  rw [owners_transport halfTurn p hf i]
  simp only [halfTurn,Transform.pull,inside_pullX,inside_pullY]

theorem half_ordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    Ordinary (owners (halfTurn.pullPacking p) 4) ↔ NorthOrdinary p := by
  simp only [Ordinary,half_inside p hf]
  norm_num [halfTurn,ownerAction,ownerSwap,ownerX,ownerY,NorthOrdinary]

theorem half_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    Inward (owners (halfTurn.pullPacking p) 4) ↔ NorthInward p := by
  simp only [Inward,half_inside p hf]
  norm_num [halfTurn,ownerAction,ownerSwap,ownerX,ownerY,NorthInward]

theorem half_north_ordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    NorthOrdinary (halfTurn.pullPacking p) ↔ Ordinary (owners p 4) := by
  simp only [NorthOrdinary,half_inside p hf]
  norm_num [halfTurn,ownerAction,ownerSwap,ownerX,ownerY,Ordinary]

theorem half_north_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    NorthInward (halfTurn.pullPacking p) ↔ Inward (owners p 4) := by
  simp only [NorthInward,half_inside p hf]
  norm_num [halfTurn,ownerAction,ownerSwap,ownerX,ownerY,Inward]

theorem north_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : NorthOrdinary p ∨ NorthInward p := by
  have cover := C1092MPPMActualNonordinary.ordinary_or_inward
    (halfTurn.pullPacking p) (family_transport halfTurn p hf) (half_context p hf hb)
  exact cover.imp ((half_ordinary p hf).mp) ((half_inward p hf).mp)

end
#print axioms north_cover
end N12Compact.C1092MPPMActualInward
