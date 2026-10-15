import Compact.Completion.OtherCases.MergedPending.UpperNegative
import Compact.Completion.OtherCases.MergedPending.NegativeUpperFaces
import Compact.Completion.OtherCases.MergedPending.SoutheastBranches

/-! Actual-owner entrances to the negative-upper face profile. In C700
the statement uses the literal transposed chart already proved in
UpperNegative. Only C683/C867 have the distinct SE512 owner used by the
last conditional branch cut. No whole-family exclusion is asserted. -/
namespace N12Compact.MergedPending
open S12 S12Pilot C977CornerCubic CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

theorem upper_negative_input (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k)
    (H : OpenSquare) (normal : Normal H.c (-H.s))
    (shape : H.side=(owner p 3072).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    NegativeUpperFaces.Input (H.translated 2 2) := by
  have marks := upper_merged_markers k p hf member
  have south := (southwest_points k p hf).2.1
  have top := (auxiliary_exact p 32768 14 (by norm_num)).mpr (common_labels k p hf).top.2
  have missing := missing_marker _ p hf 3072 member 15 (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints,S12.marker] at top missing
  refine ⟨normal,?_,?_,?_,?_,?_,?_⟩
  · change 1<H.side
    simpa only [shape] using side p 3072
  · norm_num [inside_translated_iff]
    exact (inside _ _).mpr marks.1
  · norm_num [inside_translated_iff]
    exact (inside _ _).mpr marks.2
  · norm_num [inside_translated_iff]
    exact fun own => apart _ p hf 3072 256 member (common_member k 256 (by decide))
      (by decide) _ _ ⟨(inside _ _).mp own,south⟩
  · norm_num [inside_translated_iff]
    exact fun own => apart _ p hf 3072 32768 member (common_member k 32768 (by decide))
      (by decide) _ _ ⟨(inside _ _).mp own,top⟩
  · norm_num [inside_translated_iff]
    exact fun own => missing ((inside _ _).mp own)

theorem c700_transposed_negative_input (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) (H : OpenSquare)
    (normal : Normal H.c (-H.s)) (shape : H.side=(owner p 1536).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 1536).Inside y x) :
    NegativeUpperFaces.Input (H.translated 2 2) := by
  have marks := c700_merged_markers p hf
  have south := (southwest_points .c700 p hf).1
  have right := (auxiliary_exact p 16384 8 (by norm_num)).mpr (c700_right_labels p hf).1
  have missing := missing_marker _ p hf 1536 (by decide +kernel) 14 (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints,S12.marker] at right missing
  refine ⟨normal,?_,?_,?_,?_,?_,?_⟩
  · change 1<H.side
    simpa only [shape] using side p 1536
  · norm_num [inside_translated_iff]
    exact (inside _ _).mpr marks.1
  · norm_num [inside_translated_iff]
    exact (inside _ _).mpr marks.2
  · norm_num [inside_translated_iff]
    exact fun own => apart _ p hf 1536 256 (by decide +kernel) (by decide +kernel)
      (by decide) _ _ ⟨(inside _ _).mp own,south⟩
  · norm_num [inside_translated_iff]
    exact fun own => apart _ p hf 1536 16384 (by decide +kernel) (by decide +kernel)
      (by decide) _ _ ⟨(inside _ _).mp own,right⟩
  · norm_num [inside_translated_iff]
    exact fun own => missing ((inside _ _).mp own)

/-- Under the actual outward-SE alternative, the top-marker lower-U
exit leaves only the strict displayed projection region. This is a cut
on the surviving branch, not a declaration that the branch is empty. -/
theorem upper_outward_projection (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k)
    (H : OpenSquare) (normal : Normal H.c (-H.s))
    (shape : H.side=(owner p 3072).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y)
    (missingG : ¬(owner p 512).Inside (113/50) 2)
    (topLower : (543/500)*H.s≤H.loU-2*(H.c+H.s)) :
    1000<525*H.c-961*H.s := by
  have se : 512∈family k := by
    cases k with
    | c683 => decide +kernel
    | c700 => exact False.elim ((by decide +kernel : 3072∉family .c700) member)
    | c867 => decide +kernel
  let q := H.translated 2 2
  have h : NegativeUpperFaces.Input q := upper_negative_input k p hf member H normal shape inside
  have floor : (543/500)*q.s≤q.loU := by
    change (543/500)*H.s≤H.loU-(H.c*2+H.s*2)
    nlinarith only [topLower]
  have tilt := NegativeUpperFaces.top_lower_tilt q h floor
  have bounds := normal_bounds h.normal
  have lowerAngle : 9*q.c≤ -35*q.s := by linarith only [tilt,bounds.1]
  apply lt_of_not_ge
  intro small
  have point := NegativeUpperFaces.sharp_point q h floor lowerAngle small
  norm_num [q,inside_translated_iff] at point
  exact apart _ p hf 3072 512 member se (by decide) _ _
    ⟨(inside _ _).mp point,(southeast_outward_points k p hf se missingG).2⟩

end
#print axioms upper_negative_input
#print axioms c700_transposed_negative_input
#print axioms upper_outward_projection
end N12Compact.MergedPending
