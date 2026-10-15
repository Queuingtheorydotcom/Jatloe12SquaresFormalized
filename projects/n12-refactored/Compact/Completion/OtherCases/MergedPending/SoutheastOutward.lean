import Compact.Completion.OtherCases.MergedPending.SoutheastBranches
import Compact.Cases.C868.UpperNegativeInwardCenter

/-! The inward southeast alternative is impossible in C683 and C867.
The five foreign points force the actual merged upper square to contain
the southwest near point, which already belongs strictly to A256. The
argument is independent of every frame sign. The ensuing outward frame
is a frame of the same actual SE512, not a replacement square. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

theorem southeast_missing_inward (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (upper : 3072∈family k) :
    ¬(owner p 512).Inside (113/50) 2 := by
  intro inward
  have se : 512∈family k := by
    cases k with
    | c683 => decide +kernel
    | c700 => exact False.elim ((by decide +kernel : 3072∉family .c700) upper)
    | c867 => decide +kernel
  have sw := common_member k 256 (by decide)
  have top := common_member k 32768 (by decide)
  have corner := common_member k 16 (by decide)
  have marks := upper_merged_markers k p hf upper
  have southwest := southwest_points k p hf
  have topLeft := (auxiliary_exact p 32768 14 (by norm_num)).mpr
    (common_labels k p hf).top.2
  have topRight := singleton_top _ p hf corner (113/50) le_rfl (by norm_num)
  have topMarker := seed _ p hf 32768 top (2,1543/500) (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints] at topLeft topMarker
  have point := C868.merged_inward_low_points ((owner p 3072).translated 2 2)
    (side p 3072)
    (by norm_num only [inside_translated_iff]; exact marks.1)
    (by norm_num only [inside_translated_iff]; exact marks.2)
    (by
      norm_num only [inside_translated_iff]
      exact fun own => apart _ p hf 3072 256 upper sw (by decide) _ _
        ⟨own,southwest.2.1⟩)
    (by
      norm_num only [inside_translated_iff]
      exact fun own => apart _ p hf 3072 512 upper se (by decide) _ _ ⟨own,inward⟩)
    (by
      norm_num only [inside_translated_iff]
      exact fun own => apart _ p hf 3072 32768 upper top (by decide) _ _ ⟨own,topLeft⟩)
    (by
      norm_num only [inside_translated_iff]
      exact fun own => apart _ p hf 3072 16 upper corner (by decide) _ _ ⟨own,topRight⟩)
    (by
      norm_num only [inside_translated_iff]
      exact fun own => apart _ p hf 3072 32768 upper top (by decide) _ _ ⟨own,topMarker⟩)
  have duplicate := point.1
  norm_num only [inside_translated_iff] at duplicate
  exact apart _ p hf 3072 256 upper sw (by decide) _ _ ⟨duplicate,southwest.2.2⟩

theorem southeast_outward_points_unconditional (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (upper : 3072∈family k) :
    (owner p 512).Inside (123/50) (201/100) ∧
      (owner p 512).Inside (101/40) (17/8) := by
  have se : 512∈family k := by
    cases k with
    | c683 => decide +kernel
    | c700 => exact False.elim ((by decide +kernel : 3072∉family .c700) upper)
    | c867 => decide +kernel
  exact southeast_outward_points k p hf se (southeast_missing_inward k p hf upper)

theorem southeast_outward_frame_unconditional (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (upper : 3072∈family k) :
    ∃ B : OpenSquare,0<B.c ∧ B.s<0 ∧ -B.s≤B.c ∧
      B.side=(owner p 512).side ∧
      ∀ x y,B.Inside x y↔(owner p 512).Inside x y := by
  have se : 512∈family k := by
    cases k with
    | c683 => decide +kernel
    | c700 => exact False.elim ((by decide +kernel : 3072∉family .c700) upper)
    | c867 => decide +kernel
  exact southeast_outward_frame k p hf se (southeast_missing_inward k p hf upper)

end
#print axioms southeast_missing_inward
#print axioms southeast_outward_points_unconditional
#print axioms southeast_outward_frame_unconditional
end N12Compact.MergedPending
