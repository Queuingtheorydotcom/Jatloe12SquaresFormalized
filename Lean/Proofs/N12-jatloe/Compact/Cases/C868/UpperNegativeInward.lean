import Compact.Cases.C868.SoutheastGeometry
import Compact.Completion.OtherCases.MergedPending.NegativeUpperFaces
import Compact.Completion.CommonCases.CanonicalProjection

/-! The genuine inward southeast owner eliminates one of the negative
upper square's top-marker exits. Its two distinct strict points are kept:
G6 controls the steep interval and the right crosspoint the shallow one.
This is a face reduction, not an exclusion of the remaining top-cap sector. -/
namespace N12Compact.C868.UpperNegativeInward
open S12 S12Pilot C977CornerCubic
open MergedPending.NegativeUpperFaces
set_option Elab.async false
noncomputable section

/-- No lower-U exit at the top marker is compatible with the two actual
southeast points. The rational comparison is on the entire shallow arc. -/
theorem top_upper_v (H : OpenSquare) (h : Input H)
    (missingNear : ¬H.Inside (13/50) 0)
    (missingCross : ¬H.Inside (1/2) 0) :
    H.loV+H.side≤(543/500)*H.c := by
  rcases top_marker_faces H h with floor | cap
  · exfalso
    have bounds := normal_bounds h.normal
    have cp : 0<H.c := by linarith only [bounds.1]
    have vfloor := lower_v H h
    by_cases steep : 35*H.c≤ -61*H.s
    · have short : (13/50)*H.c-(543/500)*H.s<1 := by
        linarith only [h.normal.2.1,bounds.2.2.2.2.2]
      apply missingNear
      refine ⟨?_,?_,?_,?_⟩
      · linarith only [h.northwest.1,cp,h.normal.1]
      · linarith only [floor,h.side,short]
      · linarith only [h.northwest.2.2.1,steep]
      · linarith only [vfloor,h.side,bounds.2.2.2.1]
    · have angle := top_lower_tilt H h floor
      have projection := CommonCases.CanonicalProjection.before H.c (-H.s)
        (56/65) (33/65) (1/2) (543/500)
        h.normal.2.2 (by norm_num)
        (by linarith only [steep,cp]) (by norm_num) (by norm_num)
      norm_num at projection
      have short : (1/2)*H.c-(543/500)*H.s<1 := by linarith only [projection]
      apply missingCross
      refine ⟨?_,?_,?_,?_⟩
      · linarith only [h.northwest.1,cp,h.normal.1]
      · linarith only [floor,h.side,short]
      · linarith only [h.northwest.2.2.1,angle,cp]
      · linarith only [vfloor,h.side,bounds.2.2.2.1]
  · exact cap

end
end N12Compact.C868.UpperNegativeInward

namespace N12Compact.C868
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

/-- The original family supplies every premise of the translated negative
merged profile. The near-west point belongs to A256, not to a top owner. -/
theorem negative_upper_input (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (H : OpenSquare)
    (normal : Normal H.c (-H.s))
    (shape : H.side=(owner p 3072).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    MergedPending.NegativeUpperFaces.Input (H.translated 2 2) := by
  refine ⟨normal,?_,?_,?_,?_,?_,?_⟩
  · change 1<H.side
    rw [shape,show (owner p 3072).side=p.commonSide from p.congruent _]
    exact p.side_gt_one
  · norm_num only [inside_translated_iff]
    apply (inside _ _).mpr
    simpa using seed_inside p hf 3072 (by decide +kernel) (33/20,47/20) (by decide +kernel)
  · norm_num only [inside_translated_iff]
    apply (inside _ _).mpr
    simpa using seed_inside p hf 3072 (by decide +kernel) (47/20,47/20) (by decide +kernel)
  · norm_num only [inside_translated_iff]
    intro own
    exact apart p hf 3072 256 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(inside _ _).mp own,by
        simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 1⟩
  · norm_num only [inside_translated_iff]
    intro own
    exact apart p hf 3072 32768 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(inside _ _).mp own,by
        simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 2⟩
  · norm_num only [inside_translated_iff]
    intro own
    exact apart p hf 3072 32768 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(inside _ _).mp own,by
        simpa using seed_inside p hf 32768 (by decide +kernel) (2,1543/500) (by decide +kernel)⟩

/-- In the inward branch, the original top marker necessarily lies beyond
the merged square's upper V face. The same B512 supplies both omissions. -/
theorem negative_upper_inward_top_cap (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (H : OpenSquare)
    (normal : Normal H.c (-H.s))
    (shape : H.side=(owner p 3072).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y)
    (inward : (owner p 512).Inside (113/50) 2) :
    (H.translated 2 2).loV+H.side≤(543/500)*H.c := by
  have h := negative_upper_input p hf H normal shape inside
  have crosspoint := southeast_right_crosspoint p hf inward
  apply UpperNegativeInward.top_upper_v (H.translated 2 2) h
  · norm_num only [inside_translated_iff]
    intro own
    exact apart p hf 3072 512 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(inside _ _).mp own,inward⟩
  · norm_num only [inside_translated_iff]
    intro own
    exact apart p hf 3072 512 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(inside _ _).mp own,crosspoint⟩

#print axioms UpperNegativeInward.top_upper_v
#print axioms negative_upper_input
#print axioms negative_upper_inward_top_cap
end
end N12Compact.C868
