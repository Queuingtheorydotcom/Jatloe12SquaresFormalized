import Compact.Cases.C868.Ownership
import Compact.Geometry.C868UpperPoint
import Compact.Geometry.ClosedFrames

/-! A proved geometric sector with an original-packing entrance. Both frame
signs remain explicit; this file does not assert the entire C868 exclusion. -/
namespace N12Compact.C868
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

theorem positive_frames_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (A H : OpenSquare)
    (hA : Normal A.c A.s) (hH : Normal H.c H.s)
    (sideA : A.side = (owner p 256).side)
    (sideH : H.side = (owner p 3072).side)
    (insideA : ∀ x y, A.Inside x y ↔ (owner p 256).Inside x y)
    (insideH : ∀ x y, H.Inside x y ↔ (owner p 3072).Inside x y) : False := by
  have bound (mask : Nat) : (owner p mask).side = p.commonSide := p.congruent _
  have aD : A.Inside 2 (87/50) := by
    apply (insideA _ _).mpr
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 0
  have aQ : A.Inside (87/50) 2 := by
    apply (insideA _ _).mpr
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 1
  have top : (owner p 32768).Inside (87/50) 3 := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 2
  have bottom : (owner p 1).Inside (8/5) 1 := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 3
  have left : (owner p 2).Inside 1 (8/5) := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 4
  have result := C868UpperPoint.point A H hA hH
    ((sideA.trans (bound 256)).trans ((sideH.trans (bound 3072)).symm))
    (by rw [sideA,bound]; exact p.side_gt_one)
    ((insideA _ _).mpr (by simpa using (seed_inside p hf 256 (by decide +kernel)
      (33/20,33/20) (by decide +kernel)))) aD aQ
    ((insideH _ _).mpr (by simpa using (seed_inside p hf 3072 (by decide +kernel)
      (33/20,47/20) (by decide +kernel))))
    ((insideH _ _).mpr (by simpa using (seed_inside p hf 3072 (by decide +kernel)
      (47/20,47/20) (by decide +kernel))))
    (fun point => apart p hf 256 1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨(insideA _ _).mp point,bottom⟩)
    (fun point => apart p hf 256 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨(insideA _ _).mp point,left⟩)
    (fun x y points => apart p hf 256 3072 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) x y ⟨(insideA x y).mp points.1,(insideH x y).mp points.2⟩)
  exact apart p hf 3072 32768 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ ⟨(insideH _ _).mp result,top⟩

/-- Every original packing has signed canonical frames. The all-positive
sector is excluded, so any surviving packing must have a negative frame
component for at least one of these two actual squares. -/
theorem remaining_frames (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ A H : OpenSquare,
      0 < A.c ∧ |A.s| ≤ A.c ∧ 0 < H.c ∧ |H.s| ≤ H.c ∧
      A.side = (owner p 256).side ∧ H.side = (owner p 3072).side ∧
      (∀ x y, A.Inside x y ↔ (owner p 256).Inside x y) ∧
      (∀ x y, H.Inside x y ↔ (owner p 3072).Inside x y) ∧
      (A.s < 0 ∨ H.s < 0) := by
  obtain ⟨A,ac,asc,sa,ia,_⟩ := ClosedFrames.canonical_frame (owner p 256)
  obtain ⟨H,hc,hsc,sh,ih,_⟩ := ClosedFrames.canonical_frame (owner p 3072)
  refine ⟨A,H,ac,asc,hc,hsc,sa,sh,ia,ih,?_⟩
  by_cases apos : 0 ≤ A.s
  · by_cases hs : 0 ≤ H.s
    · exact (positive_frames_impossible p hf A H
        ⟨apos,by simpa only [abs_of_nonneg apos] using asc,A.unit_normal⟩
        ⟨hs,by simpa only [abs_of_nonneg hs] using hsc,H.unit_normal⟩
        sa sh ia ih).elim
    · exact Or.inr (lt_of_not_ge hs)
  · exact Or.inl (lt_of_not_ge apos)

#print axioms positive_frames_impossible
end N12Compact.C868
