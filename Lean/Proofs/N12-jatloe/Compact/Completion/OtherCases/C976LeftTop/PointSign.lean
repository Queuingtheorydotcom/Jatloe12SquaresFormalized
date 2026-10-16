import Compact.Completion.OtherCases.C976LeftTop.PointScalars

/-! The complete nonpositive-frame argument in C976-LEFT-UPPER-POINTS
section 1. It uses only the literal singleton-segment endpoint, never a
replacement paired-corner point or an assumed top support. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints
open S12 S12Pilot
set_option Elab.async false

theorem nonpositive_impossible (q : OpenSquare) (h : Input q) (t : ℝ)
    (signed : q.s= -t) (cp : 0<q.c) (tn : 0≤t) (order : t≤q.c) : False := by
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have p := h.left
  have m := h.marker
  have a := h.inward
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_add,add_zero] at p m a
  have angle : (3/7)*q.c<t := by
    apply lt_of_not_ge
    intro small
    apply h.middle
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,add_zero]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [p.1,p.2.2.1,m.2.1,m.2.2.2,cp,tn,small]
  have upperU : (27/100)*q.c+(1/25)*t<q.loU+q.side := by
    by_cases small : t≤(38/39)*q.c
    · linarith only [m.2.1,small]
    · apply lt_of_not_ge
      intro cap
      have short := CommonCases.OutwardScalars.increasing_projection q.c t
        (27/100) (26/25) cp tn order unit (by norm_num) (by norm_num) (by norm_num)
      have cornerV : q.loV+q.side≤q.c := by
        apply le_of_not_gt
        intro high
        apply h.corner
        simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,mul_one,zero_add]
        refine ⟨?_,?_,?_,?_⟩ <;>
          linarith only [cap,short,h.side,m.2.1,a.2.2.1,high,cp,tn]
      have endpoint : ¬q.Inside 0 (-(13/50)) := by
        have missing := h.segment 1 (by norm_num) le_rfl
        norm_num at missing
        exact missing
      have lowerV : -(13/50)*q.c≤q.loV := by
        apply le_of_not_gt
        intro low
        apply endpoint
        simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_add]
        refine ⟨?_,?_,?_,?_⟩ <;> linarith only [p.1,m.2.1,a.2.2.2,low,cp,tn,order]
      have steep : (5/6)*q.c<t := by linarith only [lt_of_not_ge small,cp]
      have square := mul_pos (show 0<6*t-5*q.c by linarith only [steep])
        (show 0<6*t+5*q.c by linarith only [cp,tn])
      have shortC : (63/50)*q.c<1 := by nlinarith only [square,unit,cp]
      linarith only [cornerV,lowerV,h.side,shortC]
  apply h.lower
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,neg_mul]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [p.1,p.2.2.1,m.2.2.2,upperU,angle,cp,tn]

end N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints
