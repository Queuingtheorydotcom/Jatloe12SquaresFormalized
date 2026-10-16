import Compact.Completion.OtherCases.C976LeftTop.PointSign
import Compact.Completion.OtherCases.OrdinaryLeftTop.ScalarMargins

/-! C976-LEFT-UPPER-POINTS section 2. The lower angle comes from the
entire actual top segment, including the upper-corner tangency. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints
open S12 S12Pilot
set_option Elab.async false

theorem positive_profile (q : OpenSquare) (h : Input q)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) : Profile q := by
  have cu := (CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have p := h.left
  have m := h.marker
  have a := h.inward
  have middleV : -(1/2)*q.s≤q.loV := by
    apply le_of_not_gt
    intro low
    apply h.middle
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [p.1,m.2.1,a.2.2.2,cp,sn,order,low]
  have cornerV : q.loV+q.side≤q.c := by
    apply le_of_not_gt
    intro high
    apply h.corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [p.1,a.2.2.1,m.2.1,cp,sn,order,high]
  have lowerV : -(27/100)*q.s-(1/25)*q.c≤q.loV := by
    apply le_of_not_gt
    intro low
    apply h.lower
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [p.1,m.2.1,a.2.2.2,cp,sn,order,low]
  have sp : 0<q.s := by
    apply lt_of_not_ge
    intro zero
    linarith only [middleV,cornerV,h.side,cu,sn,zero]
  have farV : -(37/50)*q.s+q.c<q.loV+q.side := by
    linarith only [middleV,h.side,cu,sn]
  have farU : q.loU+q.side≤(37/50)*q.c+q.s := by
    apply le_of_not_gt
    intro high
    apply h.top (37/50) (by norm_num) le_rfl
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [p.1,p.2.2.1,cp,sn,order,high,farV]
  have lowerAngle : (21/65)*q.c<q.s := by
    apply lt_of_not_ge
    intro small
    have nearV : q.loV+q.side≤q.c-(11/25)*q.s := by
      apply le_of_not_gt
      intro high
      apply h.top (11/25) le_rfl (by norm_num)
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [p.1,p.2.2.1,m.2.1,cp,sn,order,small,high]
    have avoid (z : ℝ) (lo : 0≤z) (hi : z≤1) :
        ¬(-(q.loU+q.side)<(1-z)*(-((37/50)*q.c+q.s))+z*(-((11/25)*q.c+q.s)) ∧
          (1-z)*(-((37/50)*q.c+q.s))+z*(-((11/25)*q.c+q.s))< -q.loU ∧
          q.loV<(1-z)*(q.c-(37/50)*q.s)+z*(q.c-(11/25)*q.s) ∧
          (1-z)*(q.c-(37/50)*q.s)+z*(q.c-(11/25)*q.s)<q.loV+q.side) := by
      rintro ⟨u0,u1,v0,v1⟩
      apply h.top (37/50-(3/10)*z) (by linarith only [hi]) (by linarith only [lo])
      refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [u0,u1,v0,v1]
    have crossing := SegmentCorner.crossing_order (-(q.loU+q.side)) (-q.loU)
      q.loV (q.loV+q.side) (-((37/50)*q.c+q.s)) (q.c-(37/50)*q.s)
      (-((11/25)*q.c+q.s)) (q.c-(11/25)*q.s)
      (by linarith only [farU])
      (by linarith only [m.2.1,small])
      (by linarith only [p.1,cp,sn])
      (by linarith only [p.2.2.1,cp,order])
      (by linarith only [farV]) nearV avoid
    have wall : q.s*(q.loU+q.side)+q.c*(q.loV+q.side)≤1 := by
      nlinarith only [crossing,q.unit_normal]
    have first := mul_pos sp (sub_pos.mpr m.2.1)
    have last := mul_pos cp (show 0<q.loV+q.side+(1/2)*q.s-1 by
      linarith only [middleV,h.side])
    have margin := small_corner_margin q.c q.s cp sp order q.unit_normal small
    nlinarith only [wall,first,last,margin]
  have short := OrdinaryLeftTop.ScalarMargins.sixthSlopeSine q.c q.s cp sn order
    q.unit_normal (by linarith only [lowerAngle,cp])
  have nearU : q.loU+q.side≤(11/25)*q.c+q.s := by
    apply le_of_not_gt
    intro high
    apply h.top (11/25) le_rfl (by norm_num)
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [p.1,p.2.2.1,middleV,h.side,short,cp,sn,order,high]
  have upperAngle : q.s<(3/4)*q.c := by
    apply lt_of_not_ge
    intro large
    have bound := CommonCases.CanonicalProjection.after q.c q.s (4/5) (3/5)
      (26/25) (27/100) q.unit_normal (by norm_num)
      (by linarith only [large]) (by norm_num) (by norm_num)
    linarith only [bound,lowerV,cornerV,h.side]
  exact ⟨cp,sp,order,lowerAngle,upperAngle,lowerV,cornerV,nearU⟩

end N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints
