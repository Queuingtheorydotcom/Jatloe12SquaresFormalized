import Compact.Completion.FiniteCases.C975CentralPoints
import Compact.Completion.CommonCases.SingletonMissing
import Compact.Completion.OtherCases.C983.C974LocalEnding

/-! Genuine singleton-corner reductions for C975. The bottom root first
forces (1,1) into singleton1. Singleton2 therefore has the authentic
missing corner and stronger seeds. The exchanged root then excludes the
top halfpoint (1.5,3) from actual merged34816. No whole C975 exclusion
is asserted. Every root uses the same actual three named owners. -/
namespace N12Compact.FiniteCases.C975Selection
open S12 S12Pilot C975Domains C975Entrance
open N12Compact.CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

private theorem cap (p : NormalizedPacking) (mask : Nat) :
    (owner p mask).side≤1001/1000 := by
  change (p.square (ownerIndex p mask)).side≤1001/1000
  rw [p.congruent]
  exact p.side_le

private theorem markers (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) : ExactMarkers (owner p mask) (maskSupport mask) := by
  have hc := code family p hf mask member
  simpa only [hc] using coded_exact p (ownerIndex p mask)

theorem missing_zero_seeds (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owner p 1).Inside 1 1) :
    (owner p 1).Inside (91/50) 1 ∧ (owner p 1).Inside (49/25) (19/25) := by
  apply CommonCases.SingletonMissing.zero_missing_points _ (side p 1) (cap p 1) (box p 1)
    _ missing
  convert markers p hf 1 (by decide +kernel) using 1 <;> decide +kernel

theorem bottom_corner_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owner p 1).Inside 1 1) :
    C983.C974LocalData.Input ((owner p 1).translated 1 1)
      ((owner p 8192).translated 1 1) ((owner p 12).translated 1 1) := by
  have h := fixed p hf
  have seeds := missing_zero_seeds p hf missing
  have marker : (owner p 1).Inside 1 (457/500) := by
    convert seed_point p hf 1 (by decide +kernel) (1,457/500) (by decide +kernel)
      using 1 <;> norm_num
  refine {
    sideLarge := side p 1
    sameKW := (p.congruent _).trans (p.congruent _).symm
    sameKC := (p.congruent _).trans (p.congruent _).symm
    lowerWall := ?_,markerK := ?_,pointK := ?_,seedK := ?_,missingK := ?_
    originW := ?_,markerW := ?_,farW := ?_
    missingMarker := ?_,missingMiddle := ?_,missingOuter := ?_
    cornerWalls := ?_,corner := ?_,missingCorner := ?_
    apartKW := ?_,apartKC := ?_,apartWC := ?_ }
  · intro x y own
    have wall := (box p 1 _ _ ((inside_translated_iff _ _ _ _ _).mp own)).2.2.1
    linarith only [wall]
  · norm_num [inside_translated_iff]; exact marker
  · norm_num [inside_translated_iff]; exact seeds.1
  · norm_num [inside_translated_iff]; exact seeds.2
  · norm_num [inside_translated_iff]; exact missing
  · norm_num [inside_translated_iff]; exact bottom_origin p hf
  · norm_num [inside_translated_iff]; exact h.bottomMarker
  · norm_num [inside_translated_iff]; exact (bottom_reach p hf).1
  · norm_num [inside_translated_iff]; exact foreign p hf 8192 512
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ h.southeastMarker
  · norm_num [inside_translated_iff]; exact foreign p hf 8192 256
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (southwest_south p hf)
  · norm_num [inside_translated_iff]; exact foreign p hf 8192 512
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (southeast_lower p hf)
  · intro x y own
    have wall := box p 12 _ _ ((inside_translated_iff _ _ _ _ _).mp own)
    constructor <;> linarith only [wall.2.1,wall.2.2.1]
  · norm_num [inside_translated_iff]; exact h.southeastCorner
  · norm_num [inside_translated_iff]; exact foreign p hf 12 512
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (southeast_lower p hf)
  · intro x y both
    exact apart _ p hf 1 8192 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩
  · intro x y both
    exact apart _ p hf 1 12 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩
  · intro x y both
    exact apart _ p hf 8192 12 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      ⟨(inside_translated_iff _ _ _ _ _).mp both.1,(inside_translated_iff _ _ _ _ _).mp both.2⟩

/-- This is the actual corner owner, obtained by closing the opposite
missing-corner branch with the continuous three-square theorem. -/
theorem singleton_zero_corner (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 1).Inside 1 1 := by
  by_contra missing
  exact C983.C974LocalEnding.impossible _ _ _ (bottom_corner_input p hf missing)

theorem singleton_one_missing_corner (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : ¬(owner p 2).Inside 1 1 :=
  foreign p hf 2 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ (singleton_zero_corner p hf)

theorem singleton_one_strong (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 2).Inside 1 (91/50) ∧ (owner p 2).Inside (19/25) (49/25) := by
  apply CommonCases.SingletonMissing.one_missing_points _ (side p 2) (cap p 2) (box p 2)
    _ (singleton_one_missing_corner p hf)
  convert markers p hf 2 (by decide +kernel) using 1 <;> decide +kernel

/-- Under the hypothetical top halfpoint, the actual paired northwest
corner transfers the genuine left origin. -/
theorem left_origin_of_top_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (top : (owner p 34816).Inside (3/2) 3) :
    (owner p 4096).Inside 1 2 := by
  let B := pullSwap (pullY (owner p 4096))
  let K := pullSwap (pullY (owner p 192))
  have boxB := container_pullSwap _ (container_pullY _ (box p 4096))
  have boxK := container_pullSwap _ (container_pullY _ (box p 192))
  have leftMarker : (owner p 4096).Inside (457/500) 2 := by
    convert seed_point p hf 4096 (by decide +kernel) (457/500,2) (by decide +kernel)
      using 1 <;> norm_num
  have leftHigh : (owner p 4096).Inside 1 (12/5) := by
    simpa [auxPoints,fPoints,gPoints] using aux_point p 4096 11 (by norm_num)
      (compulsory p hf).leftWall.2
  have cornerMarker : (owner p 192).Inside (457/500) 3 := by
    convert seed_point p hf 192 (by decide +kernel) (457/500,3) (by decide +kernel)
      using 1 <;> norm_num
  have corner : (owner p 192).Inside 1 3 := by
    convert seed_point p hf 192 (by decide +kernel) (1,3) (by decide +kernel)
      using 1 <;> norm_num
  have point := WallProfile.boundary_origin B K (457/500) (8/5)
    (side p 4096) ((p.congruent _).trans (p.congruent _).symm)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [B]; norm_num [inside_pullSwap,inside_pullY]; exact leftMarker)
    (by dsimp only [B]; norm_num [inside_pullSwap,inside_pullY]; exact leftHigh)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY]; exact cornerMarker)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY]; exact corner)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY]
        exact foreign p hf 192 34816 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) _ _ top)
    (by
      intro x y both
      have first : (owner p 192).Inside y (4-x) := by
        simpa only [K,inside_pullSwap,inside_pullY] using both.1
      have last : (owner p 4096).Inside y (4-x) := by
        simpa only [B,inside_pullSwap,inside_pullY] using both.2
      exact apart _ p hf 192 4096 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ ⟨first,last⟩)
  dsimp only [B] at point
  norm_num [inside_pullSwap,inside_pullY] at point
  exact point

theorem left_corner_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (top : (owner p 34816).Inside (3/2) 3) :
    C983.C974LocalData.Input ((pullSwap (owner p 2)).translated 1 1)
      ((pullSwap (owner p 4096)).translated 1 1) ((pullSwap (owner p 192)).translated 1 1) := by
  have seeds := singleton_one_strong p hf
  have marker : (owner p 2).Inside (457/500) 1 := by
    convert seed_point p hf 2 (by decide +kernel) (457/500,1) (by decide +kernel)
      using 1 <;> norm_num
  have leftMarker : (owner p 4096).Inside (457/500) 2 := by
    convert seed_point p hf 4096 (by decide +kernel) (457/500,2) (by decide +kernel)
      using 1 <;> norm_num
  have corner : (owner p 192).Inside 1 3 := by
    convert seed_point p hf 192 (by decide +kernel) (1,3) (by decide +kernel)
      using 1 <;> norm_num
  refine {
    sideLarge := side p 2
    sameKW := (p.congruent _).trans (p.congruent _).symm
    sameKC := (p.congruent _).trans (p.congruent _).symm
    lowerWall := ?_,markerK := ?_,pointK := ?_,seedK := ?_,missingK := ?_
    originW := ?_,markerW := ?_,farW := ?_
    missingMarker := ?_,missingMiddle := ?_,missingOuter := ?_
    cornerWalls := ?_,corner := ?_,missingCorner := ?_
    apartKW := ?_,apartKC := ?_,apartWC := ?_ }
  · intro x y own
    have original : (owner p 2).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using own
    have wall := (box p 2 _ _ original).1
    linarith only [wall]
  · norm_num [inside_translated_iff,inside_pullSwap]; exact marker
  · norm_num [inside_translated_iff,inside_pullSwap]; exact seeds.1
  · norm_num [inside_translated_iff,inside_pullSwap]; exact seeds.2
  · norm_num [inside_translated_iff,inside_pullSwap]; exact singleton_one_missing_corner p hf
  · norm_num [inside_translated_iff,inside_pullSwap]; exact left_origin_of_top_halfpoint p hf top
  · norm_num [inside_translated_iff,inside_pullSwap]; exact leftMarker
  · norm_num [inside_translated_iff,inside_pullSwap]; exact left_reach p hf
  · norm_num [inside_translated_iff,inside_pullSwap]; exact foreign p hf 4096 34816
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (fixed p hf).northwestMarker
  · norm_num [inside_translated_iff,inside_pullSwap]; exact foreign p hf 4096 256
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (southwest_west p hf)
  · norm_num [inside_translated_iff,inside_pullSwap]; exact foreign p hf 4096 34816
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ top
  · intro x y own
    have original : (owner p 192).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using own
    have wall := box p 192 _ _ original
    constructor <;> linarith only [wall.2.2.2,wall.1]
  · norm_num [inside_translated_iff,inside_pullSwap]; exact corner
  · norm_num [inside_translated_iff,inside_pullSwap]; exact foreign p hf 192 34816
      (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ top
  · intro x y both
    exact apart _ p hf 2 4096 (by decide +kernel) (by decide +kernel) (by decide +kernel) (1+y) (1+x)
      ⟨(by simpa only [inside_translated_iff,inside_pullSwap] using both.1),
        (by simpa only [inside_translated_iff,inside_pullSwap] using both.2)⟩
  · intro x y both
    exact apart _ p hf 2 192 (by decide +kernel) (by decide +kernel) (by decide +kernel) (1+y) (1+x)
      ⟨(by simpa only [inside_translated_iff,inside_pullSwap] using both.1),
        (by simpa only [inside_translated_iff,inside_pullSwap] using both.2)⟩
  · intro x y both
    exact apart _ p hf 4096 192 (by decide +kernel) (by decide +kernel) (by decide +kernel) (1+y) (1+x)
      ⟨(by simpa only [inside_translated_iff,inside_pullSwap] using both.1),
        (by simpa only [inside_translated_iff,inside_pullSwap] using both.2)⟩

/-- The exchanged three-square ending forbids this actual merged-top
halfpoint. This is an unconditional exclusion, not an assumed foreign seed. -/
theorem top_halfpoint_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : ¬(owner p 34816).Inside (3/2) 3 := by
  intro top
  exact C983.C974LocalEnding.impossible _ _ _ (left_corner_input p hf top)

#print axioms singleton_zero_corner
#print axioms singleton_one_strong
#print axioms top_halfpoint_excluded
end
end N12Compact.FiniteCases.C975Selection
