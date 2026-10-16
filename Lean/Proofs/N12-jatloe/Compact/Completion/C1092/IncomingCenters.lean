import Compact.Completion.C1092.OppositePair

/-! Every incoming physical wall pair forces its same genuine central
owner to contain (2,2). These all-packing consequences simplify the
remaining MMMM and MMMP entrances; they are not case exclusions. -/
namespace N12Compact.C1092IncomingCenters
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092OppositePair
set_option Elab.async false

theorem southeast (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (b : WallBranch) (hb : WallContext p b)
    (right : b 2=true) (bottom : b 1=false) : (owners p 5).Inside 2 2 := by
  let g : Transform := ⟨false,true,false⟩
  have h := southwest_center (g.pullPacking p) (family_transport g p hf)
    (branchAction g b) (context_transport g p hf b hb)
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,right])
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,bottom])
  rw [owners_transport g p hf 4] at h
  norm_num [g,ownerAction,ownerX,ownerY,Transform.pull,inside_pullX] at h
  exact h

theorem northwest (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (b : WallBranch) (hb : WallContext p b)
    (left : b 0=false) (top : b 3=true) : (owners p 7).Inside 2 2 := by
  let g : Transform := ⟨false,false,true⟩
  have h := southwest_center (g.pullPacking p) (family_transport g p hf)
    (branchAction g b) (context_transport g p hf b hb)
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,left])
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,top])
  rw [owners_transport g p hf 4] at h
  norm_num [g,ownerAction,ownerX,ownerY,Transform.pull,inside_pullY] at h
  exact h

theorem exceptional (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p (canonicalBranch 1)) :
    (owners p 4).Inside 2 2 := southwest_center p hf _ hb rfl rfl

theorem adjacent (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p (canonicalBranch 2)) :
    (owners p 5).Inside 2 2 := southeast p hf _ hb rfl rfl

#print axioms exceptional
#print axioms adjacent
end N12Compact.C1092IncomingCenters
