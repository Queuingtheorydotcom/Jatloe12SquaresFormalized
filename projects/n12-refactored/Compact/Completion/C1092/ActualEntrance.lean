import Compact.Completion.C1092.InwardElbows
import Compact.Bridge.C1092WallSymmetry

/-! Actual C1092 incoming wall pairs. The whole-packing transformations
retain all twelve original squares. This supplies strict inward elbows;
it does not replace the subsequent physical two-wall center argument. -/
namespace N12Compact.C1092ActualEntrance
open S12 S12Pilot C1092WallCycle C1092WallSymmetry
set_option Elab.async false

theorem southwest_marker (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    (owners p 4).Inside (33/20) (33/20) := by
  have h : Owns (owners p 4) 8 :=
    (owners_markers p hf 4 8).mpr (by decide +kernel)
  simpa [Owns,marker] using h

theorem southwest_missing_east (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ¬ (owners p 4).Inside (47/20) (33/20) := by
  have h : ¬ Owns (owners p 4) 9 := fun h =>
    (by decide +kernel : (9 : Marker) ∉ maskSupport (ownerCode 4))
      ((owners_markers p hf 4 9).mp h)
  simpa [Owns,marker] using h

theorem southwest_missing_north (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ¬ (owners p 4).Inside (33/20) (47/20) := by
  have h : ¬ Owns (owners p 4) 11 := fun h =>
    (by decide +kernel : (11 : Marker) ∉ maskSupport (ownerCode 4))
      ((owners_markers p hf 4 11).mp h)
  simpa [Owns,marker] using h

/-- Both incoming physical wall cuts force both inward points in the same
southwest owner. The foreign-wall exclusions use actual disjointness. -/
theorem southwest_pair (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (b : WallBranch) (hb : WallContext p b)
    (left : b 0 = true) (bottom : b 1 = true) :
    (owners p 4).Inside 2 (87/50) ∧
      (owners p 4).Inside (87/50) 2 := by
  have lowLeft : (owners p 8).Inside 1 (803/500) := by
    simpa [wallOwner,pointMap,branchY,left] using
      local_wall_segment p b hb 0 (803/500) (by norm_num) (by norm_num)
  have auxLeft : (owners p 8).Inside 1 (87/50) := by
    simpa [wallOwner,pointMap,branchY,left] using wall_auxiliary_point p b hb 0
  have lowBottom : (owners p 9).Inside (803/500) 1 := by
    simpa [wallOwner,pointMap,branchY,bottom] using
      local_wall_segment p b hb 1 (803/500) (by norm_num) (by norm_num)
  have auxBottom : (owners p 9).Inside (87/50) 1 := by
    simpa [wallOwner,pointMap,branchY,bottom] using wall_auxiliary_point p b hb 1
  have side : 1 < (owners p 4).side := by
    change 1 < (p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  exact C1092InwardElbows.pair (owners p 4) side
    (southwest_marker p hf) (southwest_missing_east p hf)
    (southwest_missing_north p hf)
    (fun h => owners_disjoint p hf 4 8 (by decide) _ _ ⟨h,lowLeft⟩)
    (fun h => owners_disjoint p hf 4 8 (by decide) _ _ ⟨h,auxLeft⟩)
    (fun h => owners_disjoint p hf 4 9 (by decide) _ _ ⟨h,lowBottom⟩)
    (fun h => owners_disjoint p hf 4 9 (by decide) _ _ ⟨h,auxBottom⟩)

/-- The opposite incoming pair is obtained by transforming this same
packing through a half-turn, including all wall cuts and wall squares. -/
theorem northeast_pair (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (b : WallBranch) (hb : WallContext p b)
    (right : b 2 = false) (top : b 3 = false) :
    (owners p 6).Inside 2 (113/50) ∧
      (owners p 6).Inside (113/50) 2 := by
  let g : Transform := ⟨false,true,true⟩
  have transformed := southwest_pair (g.pullPacking p) (family_transport g p hf)
    (branchAction g b) (context_transport g p hf b hb)
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,right])
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,top])
  rw [owners_transport g p hf 4] at transformed
  norm_num [g,ownerAction,ownerX,ownerY,Transform.pull,Transform.apply,
    inside_pullX,inside_pullY] at transformed
  exact transformed

/-- A right-bottom incoming pair reaches the southeast actual owner. -/
theorem southeast_pair (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (b : WallBranch) (hb : WallContext p b)
    (right : b 2 = true) (bottom : b 1 = false) :
    (owners p 5).Inside 2 (87/50) ∧
      (owners p 5).Inside (113/50) 2 := by
  let g : Transform := ⟨false,true,false⟩
  have transformed := southwest_pair (g.pullPacking p) (family_transport g p hf)
    (branchAction g b) (context_transport g p hf b hb)
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,right])
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,bottom])
  rw [owners_transport g p hf 4] at transformed
  norm_num [g,ownerAction,ownerX,ownerY,Transform.pull,Transform.apply,
    inside_pullX,inside_pullY] at transformed
  exact transformed

/-- The left-top incoming pair reaches the northwest actual owner. -/
theorem northwest_pair (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (b : WallBranch) (hb : WallContext p b)
    (left : b 0 = false) (top : b 3 = true) :
    (owners p 7).Inside 2 (113/50) ∧
      (owners p 7).Inside (87/50) 2 := by
  let g : Transform := ⟨false,false,true⟩
  have transformed := southwest_pair (g.pullPacking p) (family_transport g p hf)
    (branchAction g b) (context_transport g p hf b hb)
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,left])
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,top])
  rw [owners_transport g p hf 4] at transformed
  norm_num [g,ownerAction,ownerX,ownerY,Transform.pull,Transform.apply,
    inside_pullX,inside_pullY] at transformed
  exact transformed

theorem opposite_branch_pairs (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (hb : WallContext p (canonicalBranch 3)) :
    ((owners p 4).Inside 2 (87/50) ∧ (owners p 4).Inside (87/50) 2) ∧
      ((owners p 6).Inside 2 (113/50) ∧ (owners p 6).Inside (113/50) 2) :=
  ⟨southwest_pair p hf _ hb (by rfl) (by rfl),
    northeast_pair p hf _ hb (by rfl) (by rfl)⟩

theorem exceptional_branch_pair (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (hb : WallContext p (canonicalBranch 1)) :
    (owners p 4).Inside 2 (87/50) ∧ (owners p 4).Inside (87/50) 2 :=
  southwest_pair p hf _ hb (by rfl) (by rfl)

theorem adjacent_branch_pair (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (hb : WallContext p (canonicalBranch 2)) :
    (owners p 5).Inside 2 (87/50) ∧ (owners p 5).Inside (113/50) 2 :=
  southeast_pair p hf _ hb (by rfl) (by rfl)

#print axioms opposite_branch_pairs
#print axioms adjacent_branch_pair
end N12Compact.C1092ActualEntrance
