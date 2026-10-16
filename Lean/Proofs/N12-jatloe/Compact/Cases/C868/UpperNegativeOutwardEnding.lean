import Compact.Cases.C868.UpperNegativeOutwardSeparation
import Compact.Cases.C868.UpperNegativeOutwardRemainingScalars
import Compact.Cases.C868.UpperNegativeNear

/-! The lower-U top-marker branch closes with the actual southwest near
point and the actual singleton-16 top-right point. Neither omission is
replaced by a different auxiliary coordinate. -/
namespace N12Compact.C868.UpperNegativeOutward
open S12 S12Pilot C977CornerCubic FourSquareAnchors ThreeSquare ABTransverse
open MergedPending.NegativeUpperFaces
set_option Elab.async false
noncomputable section

private def axisMargin (c s d t : ℝ) : ℝ :=
  1-c-(1043/500)*s+(c+s)*d+(s-c)*t-(1/5)*t*(s*d-c*t)

/-- The unit-circle identity is applied before the side and face bounds.
This preserves the exact square which owns the outward bar. -/
private theorem left_axis_gap (H B : OpenSquare) (h : Input H) (b : Faces B)
    (same : H.side=B.side) (project : 1000<525*H.c+961*(-H.s)) :
    axisMargin H.c (-H.s) B.c (-B.s)+H.loU-(543/500)*H.s≤
      H.loU+H.side-lower B H.c H.s := by
  have span : 1<B.c+(143/500)*(-B.s) := by nlinarith only [b.upperSpan]
  have steep := UpperNegativeOutwardScalars.steep_of_projection H.c (-H.s) h.normal project
  have small := UpperNegativeOutwardScalars.outward_sine_cap B.c (-B.s) b.normal span
  have hb := normal_bounds h.normal
  have bb := normal_bounds b.normal
  let P := H.c*B.c+H.s*B.s
  let Q := -H.s*B.c+H.c*B.s
  have pn : 0≤P := by
    have first := mul_nonneg (show 0≤H.c by linarith only [hb.1])
      (show 0≤B.c by linarith only [bb.1])
    have last := mul_nonneg h.normal.1 b.normal.1
    dsimp only [P]; nlinarith only [first,last]
  have qn : 0≤Q := by
    have ordered := CommonCases.UnitCircleChord.cross_order
      (show 0≤B.c by linarith only [bb.1])
      (show 0≤H.c by linarith only [hb.1]) b.normal.2.2 h.normal.2.2
      b.normal.1 h.normal.1 (by linarith only [small,steep.1])
    dsimp only [Q]; linarith only [ordered]
  have qIdentity : -H.c*B.s+H.s*B.c= -Q := by dsimp only [Q]; ring
  have formula : lower B H.c H.s=P*B.loU-Q*(B.loV+B.side) := by
    rw [C981CompletionSupportForms.lower_in_bands,qIdentity]
    change P*(B.loU+B.side/2)+(-Q)*(B.loV+B.side/2)-
      B.side/2*(|P|+|-Q|)=P*B.loU-Q*(B.loV+B.side)
    rw [abs_of_nonneg pn,abs_of_nonpos (neg_nonpos.mpr qn)]
    ring
  have identity : P*(B.c-B.s)+Q*(B.c+(4/5)*B.s)=
      H.c-H.s+(1/5)*(-B.s)*Q := by
    dsimp only [P,Q]
    linear_combination (H.c-H.s)*B.unit_normal
  have first := mul_nonneg pn (sub_nonneg.mpr b.upperU)
  have last := mul_nonneg qn (sub_nonneg.mpr b.lowerV)
  have length := mul_nonneg (show 0≤1+P+Q by linarith only [pn,qn])
    (show 0≤H.side-1 by linarith only [h.side])
  rw [formula,←same]
  rw [←same] at first
  dsimp only [axisMargin,P,Q] at first last length identity ⊢
  nlinarith only [first,last,length,identity]

theorem top_lower_impossible (H B : OpenSquare) (h : Input H) (b : Faces B)
    (same : H.side=B.side) (floor : (543/500)*H.s≤H.loU)
    (marker : B.Inside (7/20) (-7/20)) (sharp : B.Inside (21/40) (1/8))
    (near : -(1/20)*(H.c-H.s)≤H.loV)
    (topRight : (13/50)*H.c+H.s≤H.loU ∨ H.loV+H.side≤H.c-(13/50)*H.s)
    (apart : ∀ x y,¬(H.Inside x y ∧ B.Inside x y)) : False := by
  have hb := normal_bounds h.normal
  have angle := top_lower_tilt H h floor
  have project : 1000<525*H.c+961*(-H.s) := by
    apply lt_of_not_ge
    intro bound
    exact apart _ _ ⟨sharp_point H h floor
      (by linarith only [angle,hb.1]) (by nlinarith only [bound]),sharp⟩
  have span : 1<B.c+(143/500)*(-B.s) := by nlinarith only [b.upperSpan]
  have sep := separation H B h b same floor marker sharp apart
  have gap := left_axis_gap H B h b same project
  rcases topRight with lower | upper
  · have margin := UpperNegativeOutwardScalars.left_axis_weak
      H.c (-H.s) B.c (-B.s) h.normal b.normal project span
    change -(3/500:ℝ)≤axisMargin H.c (-H.s) B.c (-B.s) at margin
    nlinarith only [margin,gap,sep,lower,hb.1,h.normal.1]
  · have narrow : 1<(21/20)*H.c+(31/100)*(-H.s) := by
      linarith only [near,h.side,upper]
    have margin := UpperNegativeOutwardScalars.left_axis_margin
      H.c (-H.s) B.c (-B.s) h.normal b.normal project span narrow
    change (1/250:ℝ)≤axisMargin H.c (-H.s) B.c (-B.s) at margin
    linarith only [margin,gap,sep,floor]

end
end N12Compact.C868.UpperNegativeOutward

namespace N12Compact.C868
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

/-- Unconditional in the original packing: the inward southeast branch
is already excluded, and the outward branch rejects the other marker exit. -/
theorem negative_upper_top_cap (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (H : OpenSquare)
    (normal : Normal H.c (-H.s))
    (shapeH : H.side=(owner p 3072).side)
    (insideH : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    (H.translated 2 2).loV+H.side≤(543/500)*H.c := by
  have h := negative_upper_input p hf H normal shapeH insideH
  rcases MergedPending.NegativeUpperFaces.top_marker_faces (H.translated 2 2) h with floor | cap
  · exfalso
    have missing := southeast_outward_required p hf
    obtain ⟨B,shapeB,insideB,faces⟩ := southeast_outward_profile p hf missing
    have same : (H.translated 2 2).side=(B.translated 2 2).side := by
      change H.side=B.side
      rw [shapeH,shapeB,show (owner p 3072).side=p.commonSide from p.congruent _,
        show (owner p 512).side=p.commonSide from p.congruent _]
    apply UpperNegativeOutward.top_lower_impossible
      (H.translated 2 2) (B.translated 2 2) h faces same floor
    · norm_num only [inside_translated_iff]
      apply (insideB _ _).mpr
      simpa using seed_inside p hf 512 (by decide +kernel)
        (47/20,33/20) (by decide +kernel)
    · norm_num only [inside_translated_iff]
      exact (insideB _ _).mpr (southeast_outward_points p hf missing).2
    · exact negative_upper_near_lower p hf H normal insideH
    · exact negative_upper_top_right_faces p hf H normal insideH
    · intro x y own
      exact apart p hf 3072 512 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (2+x) (2+y)
        ⟨(insideH _ _).mp ((inside_translated_iff H 2 2 x y).mp own.1),
          (insideB _ _).mp ((inside_translated_iff B 2 2 x y).mp own.2)⟩
  · exact cap

#print axioms UpperNegativeOutward.top_lower_impossible
#print axioms negative_upper_top_cap
end
end N12Compact.C868
