import Compact.Completion.C1092.ActualEntrance
import Compact.Completion.C1092.ShortWallCenter

/-! The complete original opposite-pair BranchEnding, in its unchanged
physical wall-center contract. Its two actual central owners are forced
to contain the same strict center point. This is not an auxiliary label
classification and does not discharge the other three branch endings. -/
namespace N12Compact.C1092OppositePair
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092ActualEntrance
set_option Elab.async false

private theorem same_side (p : NormalizedPacking) (i : Fin 12) :
    (owners p i).side=p.commonSide := p.congruent _

/-- Any actual northeast incoming pair forces the physical center in its
genuine owner, using the two original walls and their closed center cuts. -/
theorem northeast_center (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (b : WallBranch) (hb : WallContext p b)
    (right : b 2=false) (top : b 3=false) : (owners p 6).Inside 2 2 := by
  have pair := northeast_pair p hf b hb right top
  have m : (owners p 6).Inside (47/20) (47/20) := by
    have own : Owns (owners p 6) 10 :=
      (owners_markers p hf 6 10).mpr (by decide +kernel)
    simpa [Owns,marker] using own
  have g : ¬ (owners p 6).Inside (47/20) (33/20) := by
    have absent : ¬ Owns (owners p 6) 9 := fun h =>
      (by decide +kernel : (9 : Marker) ∉ maskSupport (ownerCode 6))
        ((owners_markers p hf 6 9).mp h)
    simpa [Owns,marker] using absent
  have nw : ¬ (owners p 6).Inside (33/20) (47/20) := by
    have absent : ¬ Owns (owners p 6) 11 := fun h =>
      (by decide +kernel : (11 : Marker) ∉ maskSupport (ownerCode 6))
        ((owners_markers p hf 6 11).mp h)
    simpa [Owns,marker] using absent
  have rMarker : (owners p 10).Inside (1543/500) 2 := by
    have own : Owns (owners p 10) 14 :=
      (owners_markers p hf 10 14).mpr (by decide +kernel)
    simpa [Owns,marker] using own
  have tMarker : (owners p 11).Inside 2 (1543/500) := by
    have own : Owns (owners p 11) 15 :=
      (owners_markers p hf 11 15).mpr (by decide +kernel)
    simpa [Owns,marker] using own
  have rHigh : (owners p 10).Inside 3 (1197/500) := by
    have h := (hb 2).2 10
    change (owners p 10).Inside (4-1) (branchY (b 2) (803/500)) at h
    norm_num [branchY,right] at h
    exact h
  have tHigh : (owners p 11).Inside (1197/500) 3 := by
    have h := (hb 3).2 10
    change (owners p 11).Inside (branchY (b 3) (803/500)) (4-1) at h
    norm_num [branchY,top] at h
    exact h
  have rCut : 2 ≤ centerY (owners p 10) := by
    have h := (hb 2).1
    simpa [right,wallFrame,localFrame,wallOwner] using h
  have tCut : 2 ≤ centerX (owners p 11) := by
    have h := (hb 3).1
    simpa [top,wallFrame,localFrame,wallOwner] using h
  exact C1092ShortWallCenter.point (owners p 6) (owners p 10) (owners p 11)
    (by rw [same_side]; exact p.side_gt_one)
    ((same_side p 6).trans (same_side p 10).symm)
    ((same_side p 6).trans (same_side p 11).symm)
    (p.contained _) (p.contained _) rCut tCut pair.1 pair.2 m g nw
    rMarker rHigh tMarker tHigh
    (owners_disjoint p hf 6 10 (by decide))
    (owners_disjoint p hf 6 11 (by decide))

/-- The southwest conclusion uses a half-turn of the same packing.
The strict center is fixed by that simultaneous physical transformation. -/
theorem southwest_center (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (b : WallBranch) (hb : WallContext p b)
    (left : b 0=true) (bottom : b 1=true) : (owners p 4).Inside 2 2 := by
  let g : Transform := ⟨false,true,true⟩
  have transformed := northeast_center (g.pullPacking p) (family_transport g p hf)
    (branchAction g b) (context_transport g p hf b hb)
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,left])
    (by simp [g,branchAction,wallFlip,wallAction,wallX,wallY,bottom])
  rw [owners_transport g p hf 6] at transformed
  norm_num [g,ownerAction,ownerX,ownerY,Transform.pull,Transform.apply,
    inside_pullX,inside_pullY] at transformed
  exact transformed

/-- Unchanged `FourBranchEndings.oppositePair` field. -/
theorem oppositePair : BranchEnding 3 := by
  intro p hf hb
  have sw := southwest_center p hf (canonicalBranch 3) hb (by rfl) (by rfl)
  have ne := northeast_center p hf (canonicalBranch 3) hb (by rfl) (by rfl)
  exact owners_disjoint p hf 4 6 (by decide) 2 2 ⟨sw,ne⟩

#print axioms oppositePair
end N12Compact.C1092OppositePair
