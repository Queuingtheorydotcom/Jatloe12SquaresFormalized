import Compact.Cases.C868.SoutheastGeometry
import Compact.Completion.CommonCases.MergedNearPoint
import Compact.Completion.CommonCases.SouthwestPoint
import S12.Convex

/-! The inward southeast alternative supplies the missing near-right
point of the existing merged-near theorem. A literal quarter-turn of
every point then gives two strict points below the centre and the centre
itself. This argument is independent of the merged square's frame sign. -/
namespace N12Compact.C868
open S12 S12Pilot
set_option Elab.async false
noncomputable section

/-- Raw physical-square version for reuse by other merged-upper families.
Each of the five omissions is independent and is kept as an actual point. -/
theorem merged_inward_low_points (H : OpenSquare) (side : 1<H.side)
    (northwest : H.Inside (-7/20) (7/20))
    (northeast : H.Inside (7/20) (7/20))
    (missingWest : ¬H.Inside (-13/50) 0)
    (missingEast : ¬H.Inside (13/50) 0)
    (missingTopLeft : ¬H.Inside (-13/50) 1)
    (missingTopRight : ¬H.Inside (13/50) 1)
    (missingTopMarker : ¬H.Inside 0 (543/500)) :
    H.Inside (-1/20) (-1/20) ∧ H.Inside (1/20) (-1/20) ∧ H.Inside 0 0 := by
  let q := pullSwap (pullX (H.translated (-4) 0))
  have result := CommonCases.MergedNearPoint.points q side
    (by norm_num [q,inside_pullSwap,inside_pullX,inside_translated_iff]; exact northeast)
    (by norm_num [q,inside_pullSwap,inside_pullX,inside_translated_iff]; simpa only [neg_div] using northwest)
    (by norm_num [q,inside_pullSwap,inside_pullX,inside_translated_iff]; exact missingEast)
    (by norm_num [q,inside_pullSwap,inside_pullX,inside_translated_iff]; simpa only [neg_div] using missingWest)
    (by norm_num [q,inside_pullSwap,inside_pullX,inside_translated_iff]; exact missingTopRight)
    (by norm_num [q,inside_pullSwap,inside_pullX,inside_translated_iff]; simpa only [neg_div] using missingTopLeft)
    (by norm_num [q,inside_pullSwap,inside_pullX,inside_translated_iff]; exact missingTopMarker)
  norm_num [q,inside_pullSwap,inside_pullX,inside_translated_iff] at result
  have center := inside_segment H (-1/20) (-1/20) (7/20) (7/20) (1/8)
    (by simpa only [neg_div] using result.2) northeast (by norm_num) (by norm_num)
  norm_num at center
  simpa only [neg_div] using And.intro result.2 (And.intro result.1 center)

/-- The actual A256/B512 near points and the distinct T32768/C16 top
points give all five raw omissions without changing any original owner. -/
theorem upper_inward_low_points (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (inward : (owner p 512).Inside (113/50) 2) :
    (owner p 3072).Inside (39/20) (39/20) ∧
      (owner p 3072).Inside (41/20) (39/20) ∧ (owner p 3072).Inside 2 2 := by
  have result := merged_inward_low_points ((owner p 3072).translated 2 2)
    (by change 1<(owner p 3072).side
        rw [show (owner p 3072).side=p.commonSide from p.congruent _]
        exact p.side_gt_one)
    (by norm_num only [inside_translated_iff]
        simpa using seed_inside p hf 3072 (by decide +kernel) (33/20,47/20) (by decide +kernel))
    (by norm_num only [inside_translated_iff]
        simpa using seed_inside p hf 3072 (by decide +kernel) (47/20,47/20) (by decide +kernel))
    (by
      norm_num only [inside_translated_iff]
      intro own
      exact apart p hf 3072 256 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        _ _ ⟨own,by simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 1⟩)
    (by
      norm_num only [inside_translated_iff]
      intro own
      exact apart p hf 3072 512 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        _ _ ⟨own,inward⟩)
    (by
      norm_num only [inside_translated_iff]
      intro own
      exact apart p hf 3072 32768 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        _ _ ⟨own,by simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 2⟩)
    (by
      norm_num only [inside_translated_iff]
      intro own
      exact apart p hf 3072 16 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        _ _ ⟨own,by simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 1⟩)
    (by
      norm_num only [inside_translated_iff]
      intro own
      exact apart p hf 3072 32768 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        _ _ ⟨own,by simpa using seed_inside p hf 32768 (by decide +kernel) (2,1543/500) (by decide +kernel)⟩)
  norm_num only [inside_translated_iff] at result
  exact result

/-- Both singleton segments are genuine: O1 contains F2/G2 and L2
contains G0/F0. Their intermediate points are obtained by strict convexity. -/
theorem southwest_near_point (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : (owner p 256).Inside (39/20) (39/20) := by
  have bottomLow : (owner p 1).Inside (8/5) 1 := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 3
  have bottomHigh : (owner p 1).Inside (87/50) 1 := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 5
  have leftLow : (owner p 2).Inside 1 (8/5) := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 4
  have leftHigh : (owner p 2).Inside 1 (87/50) := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 6
  have bottomMiddle := inside_segment (owner p 1) (8/5) 1 (87/50) 1 (5/14)
    bottomLow bottomHigh (by norm_num) (by norm_num)
  have leftMiddle := inside_segment (owner p 2) 1 (8/5) 1 (87/50) (5/14)
    leftLow leftHigh (by norm_num) (by norm_num)
  norm_num at bottomMiddle leftMiddle
  apply CommonCases.SouthwestPoint.point (owner p 256)
  · rw [show (owner p 256).side=p.commonSide from p.congruent _]
    exact p.side_gt_one
  · simpa using seed_inside p hf 256 (by decide +kernel) (33/20,33/20) (by decide +kernel)
  · simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 0
  · simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 1
  · exact fun own => apart p hf 256 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨own,leftMiddle⟩
  · exact fun own => apart p hf 256 1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨own,bottomHigh⟩
  · exact fun own => apart p hf 256 1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨own,bottomMiddle⟩
  · exact fun own => apart p hf 256 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨own,leftHigh⟩

/-- The whole inward southeast branch is excluded, regardless of any
frame sign. Two distinct original squares would strictly own the same point. -/
theorem southeast_inward_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (inward : (owner p 512).Inside (113/50) 2) : False := by
  have upper := (upper_inward_low_points p hf inward).1
  have lower := southwest_near_point p hf
  exact apart p hf 256 3072 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ ⟨lower,upper⟩

theorem southeast_outward_required (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : ¬(owner p 512).Inside (113/50) 2 :=
  southeast_inward_impossible p hf

#print axioms merged_inward_low_points
#print axioms upper_inward_low_points
#print axioms southwest_near_point
#print axioms southeast_inward_impossible
end
end N12Compact.C868
