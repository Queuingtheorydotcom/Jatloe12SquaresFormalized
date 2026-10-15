import Compact.Cases.C868.ActualCrosspoints
import Compact.Completion.OtherCases.C1089.ContinuousBottom
import S12.CenterLocalization

/-! Continuous wall reach in the original C868 family.  Only the raw
geometric theorem from ContinuousBottom is reused, not its C1089 family
adapter.  Every segment is owned by one named original square. -/
namespace N12Compact.C868
open S12 S12Pilot
set_option Elab.async false

theorem bottom_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (x : ℝ) (low : 113/50≤x) (high : x≤14/5) :
    (owner p 8192).Inside x 1 := by
  have size : 1<(owner p 8192).side := by
    rw [show (owner p 8192).side=p.commonSide from p.congruent _]
    exact p.side_gt_one
  have far : (owner p 8192).Inside (12/5) 1 := by
    simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 4
  have separate (mask : Nat) (hm : mask∈family) (hne : 8192≠mask)
      (P : ℚ×ℚ) (hp : P∈seedPoints (maskSupport mask)) :
      ¬(owner p 8192).Inside P.1 P.2 := fun own =>
    apart p hf 8192 mask (by decide +kernel) hm hne _ _
      ⟨own,seed_inside p hf mask hm P hp⟩
  have result := Completion.OtherCases.C1089.ContinuousBottom.reach_of_far
    (owner p 8192) size (p.contained _)
    (by simpa using seed_inside p hf 8192 (by decide +kernel)
      (2,457/500) (by decide +kernel)) far
    (by simpa using separate 1 (by decide +kernel) (by decide +kernel)
      (87/50,1) (by decide +kernel))
    (by simpa using separate 1 (by decide +kernel) (by decide +kernel)
      (187/100,19/25) (by decide +kernel))
    (by simpa using separate 512 (by decide +kernel) (by decide +kernel)
      (47/20,33/20) (by decide +kernel))
  exact result.2.2 x low high

theorem left_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (y : ℝ) (low : 113/50≤y) (high : y≤14/5) :
    (owner p 4096).Inside 1 y := by
  have size : 1<(owner p 4096).side := by
    rw [show (owner p 4096).side=p.commonSide from p.congruent _]
    exact p.side_gt_one
  have near : (owner p 4096).Inside 1 (113/50) := by
    simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 2
  have far : (owner p 4096).Inside 1 (12/5) := by
    simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 3
  have separate (mask : Nat) (hm : mask∈family) (hne : 4096≠mask)
      (P : ℚ×ℚ) (hp : P∈seedPoints (maskSupport mask)) :
      ¬(owner p 4096).Inside P.1 P.2 := fun own =>
    apart p hf 4096 mask (by decide +kernel) hm hne _ _
      ⟨own,seed_inside p hf mask hm P hp⟩
  have last := C981CompletionWallAdvance.point (owner p 4096) size (p.contained _)
    (by simpa using seed_inside p hf 4096 (by decide +kernel)
      (457/500,2) (by decide +kernel)) far
    (by simpa using separate 2 (by decide +kernel) (by decide +kernel)
      (1,87/50) (by decide +kernel))
    (by simpa using separate 2 (by decide +kernel) (by decide +kernel)
      (19/25,187/100) (by decide +kernel))
    (by simpa using separate 3072 (by decide +kernel) (by decide +kernel)
      (33/20,47/20) (by decide +kernel))
  exact CommonCases.OriginalOwners.vertical_segment (owner p 4096)
    1 (113/50) (14/5) y near last (by norm_num) low high

/-- The two distinct wall markers belong to this same merged owner.
The small side cap gives a strict center interval without fixing its angle. -/
theorem right_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    9/4<centerY (owner p 16416) ∧ centerY (owner p 16416)<11/4 := by
  have low : (owner p 16416).Inside (1543/500) 2 := by
    simpa using seed_inside p hf 16416 (by decide +kernel)
      (1543/500,2) (by decide +kernel)
  have high : (owner p 16416).Inside (1543/500) 3 := by
    simpa using seed_inside p hf 16416 (by decide +kernel)
      (1543/500,3) (by decide +kernel)
  have cap : (owner p 16416).side≤1001/1000 := by
    rw [show (owner p 16416).side=p.commonSide from p.congruent _]
    exact p.side_le
  have square := mul_nonneg (sub_nonneg.mpr cap)
    (show 0≤1001/1000+(owner p 16416).side by linarith only [(owner p 16416).side_pos])
  have lowerDistance := inside_center_distance (owner p 16416) _ _ high
  have upperDistance := inside_center_distance (owner p 16416) _ _ low
  constructor
  · apply lt_of_not_ge
    intro failure
    have excess := mul_nonneg
      (show 0≤9/4-centerY (owner p 16416) by linarith only [failure])
      (show 0≤15/4-centerY (owner p 16416) by linarith only [failure])
    nlinarith only [lowerDistance,square,excess,
      sq_nonneg ((1543/500:ℝ)-centerX (owner p 16416))]
  · apply lt_of_not_ge
    intro failure
    have excess := mul_nonneg
      (show 0≤centerY (owner p 16416)-11/4 by linarith only [failure])
      (show 0≤centerY (owner p 16416)-5/4 by linarith only [failure])
    nlinarith only [upperDistance,square,excess,
      sq_nonneg ((1543/500:ℝ)-centerX (owner p 16416))]

/-- The merged right owner supplies this upper bar.  Its lower endpoint
is 2.22, not the unavailable lower-right auxiliary height 1.74. -/
theorem right_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (y : ℝ) (low : 111/50≤y) (high : y≤11/4) :
    (owner p 16416).Inside 3 y := by
  by_cases near : y≤239/100
  · have size : 1<(owner p 16416).side := by
      rw [show (owner p 16416).side=p.commonSide from p.congruent _]
      exact p.side_gt_one
    have box := container_pullX (owner p 16416) (p.contained _)
    have point := WallSignChord.chord (pullX (owner p 16416)) size
      (fun x z own => (box x z own).1)
      (by
        norm_num only [inside_pullX]
        simpa using seed_inside p hf 16416 (by decide +kernel)
          (1543/500,2) (by decide +kernel))
      (by
        intro own
        have actual := (inside_pullX _ _ _).mp own
        norm_num only at actual
        exact apart p hf 16416 3072 (by decide +kernel) (by decide +kernel)
          (by decide +kernel) _ _ ⟨actual,by
            simpa using seed_inside p hf 3072 (by decide +kernel)
              (47/20,47/20) (by decide +kernel)⟩)
      (by rw [center_pullX_y]; linarith only [(right_center p hf).1]) y low near
    have actual := (inside_pullX _ _ _).mp point
    norm_num only at actual
    exact actual
  · apply CommonCases.OriginalOwners.vertical_segment (owner p 16416)
      3 (9/4) (11/4) y
    · simpa using seed_inside p hf 16416 (by decide +kernel)
        (3,9/4) (by decide +kernel)
    · simpa using seed_inside p hf 16416 (by decide +kernel)
        (3,11/4) (by decide +kernel)
    · norm_num
    · linarith only [near]
    · exact high

#print axioms bottom_bar
#print axioms left_bar
#print axioms right_bar
end N12Compact.C868
