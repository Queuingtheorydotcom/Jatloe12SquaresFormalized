import Compact.Completion.C1092.MMMP.PointCore
import Compact.Completion.C1092.MMMP.Ending

/-! Exact remaining MMMP obligation. The universal strong NE profile is
still to be proved from the original right-component and wall context.
Supplying it here completes the unchanged BranchEnding1 contract; this
module deliberately does not assert that missing original-family lemma. -/
namespace N12Compact.C1092MMMPProfileAdapter
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MMMPEntrance C1092MMMPOrigins
open C1092MMMPPointCore C977CornerCubic
set_option Elab.async false

structure StrongNortheast (p : NormalizedPacking) where
  square : OpenSquare
  side : square.side=(owners p 6).side
  actual : ∀ x y, square.Inside x y ↔ (owners p 6).Inside (x+2) (y+2)
  normal : Normal square.c square.s
  sine : 252/373≤square.s
  faces : C1092MMMPEnding.Profile square

theorem family_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) (profile : StrongNortheast p) : False := by
  let W := (owners p 7).translated 2 2
  let N := profile.square
  have markW : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have markN : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have markSW : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have leftTip : (owners p 8).Inside 1 (239/100) := by
    have h := local_wall_segment p mmmp hb 0 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at h
    exact h
  have pair := northeast_pair p hf hb
  apply C1092MMMPEnding.impossible W N (side_gt p 7)
    ((side_same p 7 6).trans profile.side.symm) profile.normal profile.sine profile.faces
  · norm_num [W,inside_translated_iff]
    exact northwest_center p hf hb
  · norm_num [W,inside_translated_iff]
    exact northwest_left p hf hb
  · norm_num [W,inside_translated_iff]
    exact northwest_diagonal p hf hb
  · norm_num [W,inside_translated_iff]
    exact markW
  · norm_num [W,inside_translated_iff]
    intro own
    exact owners_disjoint p hf 7 4 (by decide) _ _ ⟨own,markSW⟩
  · norm_num [W,inside_translated_iff]
    intro own
    exact owners_disjoint p hf 7 8 (by decide) _ _ ⟨own,leftTip⟩
  · apply (profile.actual _ _).mpr
    convert markN using 1 <;> norm_num
  · apply (profile.actual _ _).mpr
    convert pair.2 using 1 <;> norm_num
  · apply (profile.actual _ _).mpr
    convert pair.1 using 1 <;> norm_num
  · intro x y own
    have first := (inside_translated_iff (owners p 7) 2 2 x y).mp own.1
    have last := (profile.actual x y).mp own.2
    exact owners_disjoint p hf 7 6 (by decide) _ _
      ⟨first,by simpa only [add_comm] using last⟩

/-- A conditional bridge with its outstanding universal premise explicit.
It must not be installed as a completed field without that premise. -/
theorem branch_of_profile
    (derive : ∀ (p : NormalizedPacking), codedMarkerFamily p=family →
      WallContext p mmmp → StrongNortheast p) : BranchEnding 1 := by
  intro p hf hb
  let g : Transform := ⟨false,false,true⟩
  have action : branchAction g (canonicalBranch 1)=mmmp := by
    funext k
    fin_cases k <;> decide +kernel
  have context := context_transport g p hf (canonicalBranch 1) hb
  rw [action] at context
  have family' := family_transport g p hf
  exact family_impossible (g.pullPacking p) family' context (derive _ family' context)

#print axioms family_impossible
#print axioms branch_of_profile
end N12Compact.C1092MMMPProfileAdapter
