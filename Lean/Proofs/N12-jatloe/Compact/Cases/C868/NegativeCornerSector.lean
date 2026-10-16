import Compact.Cases.C868.PositiveSector
import Compact.Geometry.C868UpperPointNegative
import Compact.Geometry.SouthwestNegativeCorner
import Compact.Geometry.SouthwestCentralReach

/-! The negative lower-square / positive upper-square sector with its
original corner-root hypothesis retained explicitly. No auxiliary point or
physical neighbour is replaced by an assumed centre bound. -/
namespace N12Compact.C868
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

theorem negative_corner_frames_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (A H : OpenSquare)
    (hA : Normal A.c (-A.s)) (hH : Normal H.c H.s)
    (sideA : A.side = (owner p 256).side)
    (sideH : H.side = (owner p 3072).side)
    (insideA : ∀ x y, A.Inside x y ↔ (owner p 256).Inside x y)
    (insideH : ∀ x y, H.Inside x y ↔ (owner p 3072).Inside x y)
    (corner : ¬ (owner p 1).Inside 1 1) : False := by
  have shape (mask : Nat) : (owner p mask).side = p.commonSide := p.congruent _
  have size : 1 < A.side := by rw [sideA,shape]; exact p.side_gt_one
  have aSW : A.Inside (33/20) (33/20) := (insideA _ _).mpr (by
    simpa using seed_inside p hf 256 (by decide +kernel)
      (33/20,33/20) (by decide +kernel))
  have aD : A.Inside 2 (87/50) := (insideA _ _).mpr (by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 0)
  have aQ : A.Inside (87/50) 2 := (insideA _ _).mpr (by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 1)
  have hNW : H.Inside (33/20) (47/20) := (insideH _ _).mpr (by
    simpa using seed_inside p hf 3072 (by decide +kernel)
      (33/20,47/20) (by decide +kernel))
  have hNE : H.Inside (47/20) (47/20) := (insideH _ _).mpr (by
    simpa using seed_inside p hf 3072 (by decide +kernel)
      (47/20,47/20) (by decide +kernel))
  have aApart (mask : Nat) (hm : mask ∈ family) (hne : 256 ≠ mask) :
      ∀ x y, ¬ (A.Inside x y ∧ (owner p mask).Inside x y) := by
    intro x y points
    exact apart p hf 256 mask (by decide +kernel) hm hne x y
      ⟨(insideA x y).mp points.1,points.2⟩
  have aMissing (mask : Nat) (hm : mask ∈ family) (hne : 256 ≠ mask)
      (P : ℚ × ℚ) (hp : P ∈ seedPoints (maskSupport mask)) :
      ¬ A.Inside P.1 P.2 :=
    fun h => aApart mask hm hne _ _ ⟨h,seed_inside p hf mask hm P hp⟩
  have oN : (owner p 1).Inside (28/25) 1 := by
    simpa using seed_inside p hf 1 (by decide +kernel) (28/25,1) (by decide +kernel)
  have oW : (owner p 1).Inside (87/50) 1 := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 5
  have lN : (owner p 2).Inside 1 (28/25) := by
    simpa using seed_inside p hf 2 (by decide +kernel) (1,28/25) (by decide +kernel)
  have lW : (owner p 2).Inside 1 (87/50) := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 6
  have left := SouthwestCentralReach.left A (owner p 1) size aSW aD aQ
    (by simpa using aMissing 3072 (by decide +kernel) (by decide +kernel) (47/20,47/20) (by decide +kernel))
    (by simpa using aMissing 3072 (by decide +kernel) (by decide +kernel) (33/20,47/20) (by decide +kernel))
    (by simpa using aMissing 512 (by decide +kernel) (by decide +kernel) (47/20,33/20) (by decide +kernel))
    oN oW (aApart 1 (by decide +kernel) (by decide +kernel))
  have centre := SouthwestNegativeCorner.point (owner p 1) A (owner p 2)
    (-A.s) (by ring) hA ((shape 1).trans ((sideA.trans (shape 256)).symm))
    size (p.contained _)
    (by simpa using seed_inside p hf 1 (by decide +kernel) (1,457/500) (by decide +kernel)) oN
    (by simpa using seed_inside p hf 1 (by decide +kernel) (187/100,19/25) (by decide +kernel)) corner
    (fun h => apart p hf 1 8192 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨h,by simpa using seed_inside p hf 8192 (by decide +kernel) (2,457/500) (by decide +kernel)⟩)
    aSW aD aQ left lN lW
    (fun x y h => aApart 1 (by decide +kernel) (by decide +kernel) x y ⟨h.2,h.1⟩)
    (aApart 2 (by decide +kernel) (by decide +kernel))
  have high := C868UpperPointNegative.point A H hA hH
    ((sideA.trans (shape 256)).trans ((sideH.trans (shape 3072)).symm))
    size aSW aD aQ centre hNW hNE
    (fun x y h => aApart 3072 (by decide +kernel) (by decide +kernel) x y
      ⟨h.1,(insideH x y).mp h.2⟩)
  have top : (owner p 32768).Inside (87/50) 3 := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 2
  exact apart p hf 3072 32768 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ ⟨(insideH _ _).mp high,top⟩

#print axioms negative_corner_frames_impossible

/-- The remaining alternatives are statements about actual packing squares.
This records the exact residue instead of treating the conditional centre
theorem as a completed orientation argument. -/
theorem remaining_canonical_frames (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ A H : OpenSquare,
      0 < A.c ∧ |A.s| ≤ A.c ∧ 0 < H.c ∧ |H.s| ≤ H.c ∧
      A.side = (owner p 256).side ∧ H.side = (owner p 3072).side ∧
      (∀ x y, A.Inside x y ↔ (owner p 256).Inside x y) ∧
      (∀ x y, H.Inside x y ↔ (owner p 3072).Inside x y) ∧
      (H.s < 0 ∨ A.s < 0 ∧ (owner p 1).Inside 1 1) := by
  classical
  obtain ⟨A,H,ac,asc,hc,hsc,sa,sh,ia,ih,remaining⟩ := remaining_frames p hf
  refine ⟨A,H,ac,asc,hc,hsc,sa,sh,ia,ih,?_⟩
  by_cases hs : H.s < 0
  · exact Or.inl hs
  · have hnonnegative : 0 ≤ H.s := le_of_not_gt hs
    have anegative : A.s < 0 := remaining.resolve_right hs
    right
    refine ⟨anegative,?_⟩
    by_contra absent
    exact negative_corner_frames_impossible p hf A H
      ⟨by linarith only [anegative],
        by simpa only [abs_of_neg anegative] using asc,
        by nlinarith only [A.unit_normal]⟩
      ⟨hnonnegative,by simpa only [abs_of_nonneg hnonnegative] using hsc,H.unit_normal⟩
      sa sh ia ih absent

end N12Compact.C868
