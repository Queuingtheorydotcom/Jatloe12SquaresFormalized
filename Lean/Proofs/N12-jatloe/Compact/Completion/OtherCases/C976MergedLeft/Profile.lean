import Compact.Completion.OtherCases.C976MergedLeft.Scalars

/-! The original top segment, rather than its two endpoints alone,
forces the positive-angle profile in section 3 of the merged-left proof. -/
namespace N12Compact.Completion.OtherCases.C976MergedLeft
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
  have lowerAngle : (38/65)*q.c<q.s := by
    apply lt_of_not_ge
    intro small
    have nearV : q.loV+q.side≤q.c-(27/100)*q.s := by
      apply le_of_not_gt
      intro high
      apply h.top (27/100) le_rfl (by norm_num)
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [p.1,p.2.2.1,m.2.1,cp,sn,order,small,high]
    have avoid (z : ℝ) (lo : 0≤z) (hi : z≤1) :
        ¬(-(q.loU+q.side)<(1-z)*(-((37/50)*q.c+q.s))+z*(-((27/100)*q.c+q.s)) ∧
          (1-z)*(-((37/50)*q.c+q.s))+z*(-((27/100)*q.c+q.s))< -q.loU ∧
          q.loV<(1-z)*(q.c-(37/50)*q.s)+z*(q.c-(27/100)*q.s) ∧
          (1-z)*(q.c-(37/50)*q.s)+z*(q.c-(27/100)*q.s)<q.loV+q.side) := by
      rintro ⟨u0,u1,v0,v1⟩
      apply h.top (37/50-(47/100)*z) (by linarith only [hi]) (by linarith only [lo])
      refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [u0,u1,v0,v1]
    have crossing := SegmentCorner.crossing_order (-(q.loU+q.side)) (-q.loU)
      q.loV (q.loV+q.side) (-((37/50)*q.c+q.s)) (q.c-(37/50)*q.s)
      (-((27/100)*q.c+q.s)) (q.c-(27/100)*q.s)
      (by linarith only [farU])
      (by linarith only [m.2.1,small])
      (by linarith only [p.1,cp,sn])
      (by linarith only [p.2.2.1,cp,order])
      (by nlinarith only [farV]) nearV avoid
    have wall : q.s*(q.loU+q.side)+q.c*(q.loV+q.side)≤1 := by
      nlinarith only [crossing,q.unit_normal]
    have first := mul_pos sp (sub_pos.mpr m.2.1)
    have last := mul_pos cp (show 0<q.loV+q.side+(1/2)*q.s-1 by
      linarith only [middleV,h.side])
    have margin := small_corner_margin q.c q.s cp sp order q.unit_normal small
    nlinarith only [wall,first,last,margin]
  have short := top_span q.c q.s q.unit_normal lowerAngle.le
  have nearU : q.loU+q.side≤(27/100)*q.c+q.s := by
    apply le_of_not_gt
    intro high
    apply h.top (27/100) le_rfl (by norm_num)
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [p.1,p.2.2.1,middleV,h.side,short,cp,sn,order,high]
  exact ⟨cp,sp,order,lowerAngle,middleV,cornerV,nearU⟩

end N12Compact.Completion.OtherCases.C976MergedLeft
