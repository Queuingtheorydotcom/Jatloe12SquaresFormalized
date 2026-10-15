import Compact.Geometry.C977CornerCubic

/-! A short negative-SE halfpoint argument. Genuine omissions of both
southwest points, and the actual right-wall origin, are essential. The
two forced widths contradict the canonical normal sum bound with weights
38 and25. There is no sign conclusion for a different physical square.
This is source only, without a compiler replay. -/
namespace N12Compact.FiniteCases.C972Local
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

theorem negative_point (q : OpenSquare) (t : ℝ) (signed : q.s= -t)
    (normal : Normal q.c t) (side : 1<q.side)
    (g6 : q.Inside (13/50) 0) (f8 : q.Inside 1 (-13/50))
    (g8 : q.Inside 1 (-2/5))
    (rightOrigin : ¬q.Inside 1 0)
    (southwestNear : ¬q.Inside 0 (-13/50))
    (southwestHalf : ¬q.Inside 0 (-1/2)) : q.Inside 1 (-1/2) := by
  have bounds := normal_bounds normal
  have cp : 0<q.c := by linarith only [bounds.1]
  have g := g6
  have f := f8
  have b := g8
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,
    add_zero,zero_add,mul_one] at g f b
  have originCap : q.loV+q.side≤t := by
    apply le_of_not_gt
    intro high
    apply rightOrigin
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,add_zero,mul_one]
    refine ⟨?_,?_,?_,high⟩
    · linarith only [g.1,cp]
    · linarith only [f.2.1,normal.1]
    · linarith only [g.2.2.1,normal.1]
  by_contra missing
  have targetCap : q.loU+q.side≤q.c+t/2 := by
    apply le_of_not_gt
    intro high
    apply missing
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one]
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [g.1,cp,normal.1]
    · linarith only [high]
    · linarith only [originCap,side,bounds.2.1]
    · linarith only [b.2.2.2,cp]
  have halfFloor : -q.c/2≤q.loV := by
    apply le_of_not_gt
    intro lowV
    by_cases lowU : t/2≤q.loU
    · linarith only [lowU,targetCap,side,bounds.2.1]
    · apply southwestHalf
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,zero_add]
      refine ⟨?_,?_,?_,?_⟩
      · linarith only [lowU]
      · linarith only [b.2.1,cp,normal.2.1]
      · linarith only [lowV]
      · linarith only [b.2.2.2,cp,normal.1]
  have nearFloor : (13/50)*t≤q.loU := by
    apply le_of_not_gt
    intro lowU
    by_cases lowV : -(13/50)*q.c≤q.loV
    · have short : t+(13/50)*q.c≤9/10 := by
        linarith only [bounds.2.2.2.2.2,normal.2.1]
      linarith only [lowV,originCap,short,side]
    · apply southwestNear
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,zero_add]
      refine ⟨?_,?_,?_,?_⟩
      · linarith only [lowU]
      · linarith only [b.2.1,cp,normal.1]
      · linarith only [lowV]
      · linarith only [f.2.2.2,normal.1]
  have firstWidth : q.side≤t+q.c/2 := by
    linarith only [originCap,halfFloor]
  have secondWidth : q.side≤q.c+(6/25)*t := by
    linarith only [targetCap,nearFloor]
  -- 38*firstWidth +25*secondWidth gives63*side≤44*(c+t)≤440/7<63.
  linarith only [firstWidth,secondWidth,side,bounds.2.2.2.2.2]

theorem negative_point_original (q : OpenSquare)
    (normal : Normal q.c (-q.s)) (side : 1<q.side)
    (g6 : q.Inside (113/50) 2) (f8 : q.Inside 3 (87/50))
    (g8 : q.Inside 3 (8/5))
    (rightOrigin : ¬q.Inside 3 2)
    (southwestNear : ¬q.Inside 2 (87/50))
    (southwestHalf : ¬q.Inside 2 (3/2)) : q.Inside 3 (3/2) := by
  have answer := negative_point (q.translated 2 2) (-q.s)
    (by change q.s= -(-q.s); ring) normal side
    (by norm_num [inside_translated_iff]; exact g6)
    (by norm_num [inside_translated_iff]; exact f8)
    (by norm_num [inside_translated_iff]; exact g8)
    (by norm_num [inside_translated_iff]; exact rightOrigin)
    (by norm_num [inside_translated_iff]; exact southwestNear)
    (by norm_num [inside_translated_iff]; exact southwestHalf)
  norm_num [inside_translated_iff] at answer
  exact answer

#print axioms negative_point
#print axioms negative_point_original
end N12Compact.FiniteCases.C972Local
