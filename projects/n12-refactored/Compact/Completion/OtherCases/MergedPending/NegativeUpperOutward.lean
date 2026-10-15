import Compact.Completion.OtherCases.MergedPending.SoutheastOutward
import Compact.Completion.OtherCases.MergedPending.NegativeUpperActual
import Compact.Cases.C868.UpperNegativeCapFaces

/-! The complete outward top-marker reduction transfers to C683 and
C867 with literal original owners. C683 does not acquire a right-wall
owner: the right-marker omission is read from B512's exact marker code.
The paired corner and the whole actual bottom bar remain unchanged. -/
namespace N12Compact.MergedPending
open S12 S12Pilot C977CornerCubic CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

private theorem southeast_member (k : Case) (upper : 3072∈family k) : 512∈family k := by
  cases k with
  | c683 => decide +kernel
  | c700 => exact False.elim ((by decide +kernel : 3072∉family .c700) upper)
  | c867 => decide +kernel

theorem upper_near_lower (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k)
    (H : OpenSquare) (normal : Normal H.c (-H.s))
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    -(1/20)*(H.c-H.s)≤(H.translated 2 2).loV := by
  have marks := upper_merged_markers k p hf member
  apply C868.UpperNegativeNear.lower_v (H.translated 2 2) normal
  · norm_num only [inside_translated_iff]
    exact (inside _ _).mpr marks.1
  · norm_num only [inside_translated_iff]
    exact (inside _ _).mpr marks.2
  · norm_num only [inside_translated_iff]
    intro own
    exact apart _ p hf 3072 256 member (common_member k 256 (by decide))
      (by decide) _ _ ⟨(inside _ _).mp own,(southwest_points k p hf).2.2⟩

theorem upper_top_right_faces (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k)
    (H : OpenSquare) (normal : Normal H.c (-H.s))
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    (13/50)*H.c+H.s≤(H.translated 2 2).loU ∨
      (H.translated 2 2).loV+H.side≤H.c-(13/50)*H.s := by
  apply C868.UpperNegativeNear.top_right_faces (H.translated 2 2) normal
  · norm_num only [inside_translated_iff]
    exact (inside _ _).mpr (upper_merged_markers k p hf member).2
  · norm_num only [inside_translated_iff]
    intro own
    exact apart _ p hf 3072 16 member (common_member k 16 (by decide))
      (by decide) _ _ ⟨(inside _ _).mp own,
        (walls k p hf).topSingleton (113/50) le_rfl (by norm_num)⟩

theorem southeast_full_outward_profile (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (upper : 3072∈family k) :
    ∃ B : OpenSquare,B.side=(owner p 512).side ∧
      (∀ x y,B.Inside x y↔(owner p 512).Inside x y) ∧
      C868.UpperNegativeOutward.Faces (B.translated 2 2) := by
  have se := southeast_member k upper
  have corner := common_member k 12 (by decide)
  have bottom := common_member k 8192 (by decide)
  have marker := seed _ p hf 512 se (47/20,33/20) (by decide +kernel)
  have outward := (auxiliary_exact p 512 8 (by norm_num)).mpr (southeast_lower k p hf se)
  have missingRight := missing_marker _ p hf 512 se 14 (by decide +kernel)
  have cornerPoint := seed _ p hf 12 corner (3,1) (by decide +kernel)
  have cornerMarker := seed _ p hf 12 corner (1543/500,1) (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints,S12.marker] at marker outward missingRight cornerPoint cornerMarker
  obtain ⟨B,cp,sn,order,shape,inside⟩ := southeast_outward_frame_unconditional k p hf upper
  have normal : Normal B.c (-B.s) :=
    ⟨by linarith only [sn],order,by nlinarith only [B.unit_normal]⟩
  refine ⟨B,shape,inside,?_⟩
  apply C868.UpperNegativeOutward.faces_original B normal
    (by simpa only [shape] using side p 512)
    ((inside _ _).mpr marker) ((inside _ _).mpr outward)
  · exact fun own => southeast_missing_inward k p hf upper ((inside _ _).mp own)
  · exact fun own => missingRight ((inside _ _).mp own)
  · exact fun own => apart _ p hf 512 12 se corner (by decide) _ _
      ⟨(inside _ _).mp own,cornerPoint⟩
  · exact fun own => apart _ p hf 512 12 se corner (by decide) _ _
      ⟨(inside _ _).mp own,cornerMarker⟩
  · intro x low high own
    exact apart _ p hf 512 8192 se bottom (by decide) x 1
      ⟨(inside _ _).mp own,(bottom_reach k p hf).2 x low high⟩

/-- The lower-U marker exit is now excluded in both actual upper-merged
families. The remaining upper-V face is not a whole-case contradiction. -/
theorem upper_top_cap (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k)
    (H : OpenSquare) (normal : Normal H.c (-H.s))
    (shapeH : H.side=(owner p 3072).side)
    (insideH : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    (H.translated 2 2).loV+H.side≤(543/500)*H.c := by
  have h := upper_negative_input k p hf member H normal shapeH insideH
  rcases NegativeUpperFaces.top_marker_faces (H.translated 2 2) h with floor | cap
  · exfalso
    have se := southeast_member k member
    obtain ⟨B,shapeB,insideB,faces⟩ := southeast_full_outward_profile k p hf member
    have same : (H.translated 2 2).side=(B.translated 2 2).side := by
      change H.side=B.side
      rw [shapeH,shapeB,show (owner p 3072).side=p.commonSide from p.congruent _,
        show (owner p 512).side=p.commonSide from p.congruent _]
    apply C868.UpperNegativeOutward.top_lower_impossible
      (H.translated 2 2) (B.translated 2 2) h faces same floor
    · norm_num only [inside_translated_iff]
      apply (insideB _ _).mpr
      simpa using seed _ p hf 512 se (47/20,33/20) (by decide +kernel)
    · norm_num only [inside_translated_iff]
      exact (insideB _ _).mpr (southeast_outward_points_unconditional k p hf member).2
    · exact upper_near_lower k p hf member H normal insideH
    · exact upper_top_right_faces k p hf member H normal insideH
    · intro x y own
      exact apart _ p hf 3072 512 member se (by decide) (2+x) (2+y)
        ⟨(insideH _ _).mp ((inside_translated_iff H 2 2 x y).mp own.1),
          (insideB _ _).mp ((inside_translated_iff B 2 2 x y).mp own.2)⟩
  · exact cap

theorem upper_shallow (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k)
    (H : OpenSquare) (normal : Normal H.c (-H.s))
    (shape : H.side=(owner p 3072).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) : -3*H.s<2*H.c := by
  exact C868.UpperNegativeNear.top_cap_tilt (H.translated 2 2) normal
    (by change 1<H.side; simpa only [shape] using side p 3072)
    (upper_near_lower k p hf member H normal inside)
    (upper_top_cap k p hf member H normal shape inside)

/-- Both sharp southeast points belong to the same actual B512. Their
omission from H gives the two upper-U caps and the strict lower tilt span. -/
theorem upper_southeast_caps (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k)
    (H : OpenSquare) (normal : Normal H.c (-H.s))
    (shape : H.side=(owner p 3072).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    (H.translated 2 2).loU+H.side≤(21/40)*H.c+(1/8)*H.s ∧
    (H.translated 2 2).loU+H.side≤(23/50)*H.c+(1/100)*H.s ∧
    1<(18/25)*H.c-(99/100)*H.s := by
  have input := upper_negative_input k p hf member H normal shape inside
  have cap := upper_top_cap k p hf member H normal shape inside
  have points := southeast_outward_points_unconditional k p hf member
  have se := southeast_member k member
  have sharpMissing : ¬(H.translated 2 2).Inside (21/40) (1/8) := by
    norm_num only [inside_translated_iff]
    intro own
    exact apart _ p hf 3072 512 member se (by decide) _ _
      ⟨(inside _ _).mp own,points.2⟩
  have nearMissing : ¬(H.translated 2 2).Inside (23/50) (1/100) := by
    norm_num only [inside_translated_iff]
    intro own
    exact apart _ p hf 3072 512 member se (by decide) _ _
      ⟨(inside _ _).mp own,points.1⟩
  have sharp := C868.UpperNegativeCap.sharp_upper
    (H.translated 2 2) input cap sharpMissing
  have tilt := C868.UpperNegativeCap.lower_tilt (H.translated 2 2) input sharp
  have near := C868.UpperNegativeCap.near_upper
    (H.translated 2 2) input cap tilt nearMissing
  exact ⟨sharp,near,C868.UpperNegativeCap.span (H.translated 2 2) input near⟩

end
#print axioms southeast_full_outward_profile
#print axioms upper_top_cap
#print axioms upper_shallow
#print axioms upper_southeast_caps
end N12Compact.MergedPending
