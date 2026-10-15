import Compact.Cases.C868.UpperNegativeInwardCenter
import Compact.Completion.OtherCases.MergedPending.NegativeUpperFaces
import Compact.Completion.CommonCases.CanonicalProjection

/-! The actual southwest duplicate point strengthens the merged upper
square's lower face. This genuine extra neighbor is retained in the
remaining outward branch, including its near-diagonal orientations. -/
namespace N12Compact.C868.UpperNegativeNear
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

theorem lower_v (H : OpenSquare) (normal : Normal H.c (-H.s))
    (northwest : H.Inside (-7/20) (7/20))
    (northeast : H.Inside (7/20) (7/20))
    (missing : ¬H.Inside (-1/20) (-1/20)) :
    -(1/20)*(H.c-H.s)≤H.loV := by
  have bounds := normal_bounds normal
  have cp : 0<H.c := by linarith only [bounds.1]
  apply le_of_not_gt
  intro low
  apply missing
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [northwest.1,cp,normal.1]
  · linarith only [northeast.2.1,cp,normal.2.1]
  · linarith only [low]
  · linarith only [northwest.2.2.2,cp,normal.2.1]

/-- Together with the top-marker upper-face alternative, the actual
near-point floor gives a sharper full-interval tilt bound. -/
theorem top_cap_tilt (H : OpenSquare) (normal : Normal H.c (-H.s))
    (side : 1<H.side) (floor : -(1/20)*(H.c-H.s)≤H.loV)
    (cap : H.loV+H.side≤(543/500)*H.c) : -3*H.s<2*H.c := by
  have bounds := normal_bounds normal
  have cp : 0<H.c := by linarith only [bounds.1]
  have span : 1<(142/125)*H.c-(1/20)*H.s := by linarith only [side,floor,cap]
  apply lt_of_not_ge
  intro steep
  have projection := CommonCases.CanonicalProjection.after H.c (-H.s) (45/53) (28/53)
    (142/125) (1/20) normal.2.2 (by norm_num)
    (by linarith only [steep,cp]) (by norm_num) (by norm_num)
  norm_num at projection
  linarith only [span,projection]

/-- The genuine top-right point has only these two possible exits.
Both weak alternatives are retained, including corner tangency. -/
theorem top_right_faces (H : OpenSquare) (normal : Normal H.c (-H.s))
    (northeast : H.Inside (7/20) (7/20))
    (missing : ¬H.Inside (13/50) 1) :
    (13/50)*H.c+H.s≤H.loU ∨
      H.loV+H.side≤H.c-(13/50)*H.s := by
  have bounds := normal_bounds normal
  have cp : 0<H.c := by linarith only [bounds.1]
  by_cases low : (13/50)*H.c+H.s≤H.loU
  · exact Or.inl low
  · right
    apply le_of_not_gt
    intro high
    apply missing
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [low]
    · linarith only [northeast.2.1,cp,normal.1]
    · linarith only [northeast.2.2.1,cp,normal.2.1]
    · linarith only [high]

end N12Compact.C868.UpperNegativeNear

namespace N12Compact.C868
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

theorem negative_upper_near_lower (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (H : OpenSquare)
    (normal : Normal H.c (-H.s))
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    -(1/20)*(H.c-H.s)≤(H.translated 2 2).loV := by
  apply UpperNegativeNear.lower_v (H.translated 2 2) normal
  · norm_num only [inside_translated_iff]
    apply (inside _ _).mpr
    simpa using seed_inside p hf 3072 (by decide +kernel) (33/20,47/20) (by decide +kernel)
  · norm_num only [inside_translated_iff]
    apply (inside _ _).mpr
    simpa using seed_inside p hf 3072 (by decide +kernel) (47/20,47/20) (by decide +kernel)
  · norm_num only [inside_translated_iff]
    intro own
    exact apart p hf 3072 256 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(inside _ _).mp own,southwest_near_point p hf⟩

theorem negative_upper_top_right_faces (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (H : OpenSquare)
    (normal : Normal H.c (-H.s))
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    (13/50)*H.c+H.s≤(H.translated 2 2).loU ∨
      (H.translated 2 2).loV+H.side≤H.c-(13/50)*H.s := by
  apply UpperNegativeNear.top_right_faces (H.translated 2 2) normal
  · norm_num only [inside_translated_iff]
    apply (inside _ _).mpr
    simpa using seed_inside p hf 3072 (by decide +kernel) (47/20,47/20) (by decide +kernel)
  · norm_num only [inside_translated_iff]
    intro own
    exact apart p hf 3072 16 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(inside _ _).mp own,additional_inside p hf 1⟩

#print axioms UpperNegativeNear.lower_v
#print axioms UpperNegativeNear.top_cap_tilt
#print axioms UpperNegativeNear.top_right_faces
#print axioms negative_upper_near_lower
#print axioms negative_upper_top_right_faces
end N12Compact.C868
