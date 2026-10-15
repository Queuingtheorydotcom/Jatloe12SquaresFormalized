import Compact.Completion.OtherCases.OrdinaryBarCrosspoint.Inputs

/-! ORDINARY-BAR-CROSSPOINT.md section 1. Both endpoint exits are
obtained from the actual strict anchors. The full foreign bar then forces
a weak closed-vertex support, incompatible with the two upper caps. -/
namespace N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint
open S12 S12Pilot
set_option Elab.async false

theorem positive (q : OpenSquare) (h : Input q)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) : q.Inside (1/2) 0 := by
  by_contra missing
  have bounds := CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal
  have cu := bounds.2.1
  have m := h.marker
  have a := h.near
  have missingF := h.segment (13/50) le_rfl (by norm_num)
  have missingT := h.segment (22/25) (by norm_num) le_rfl
  have upperV : q.loV+q.side≤ -(1/2)*q.s := by
    apply le_of_not_gt
    intro high
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [m.1,m.2.2.1,a.2.1,cp,sn,order,high]
  have rightLowerU : q.loU<(543/500)*q.c := by
    linarith only [m.1,cp,sn]
  have rightLowerV : q.loV< -(543/500)*q.s := by
    linarith only [upperV,h.side,cu,sn,order]
  have upperU : q.loU+q.side≤(543/500)*q.c := by
    apply le_of_not_gt
    intro high
    have rightUpperV : q.loV+q.side≤ -(543/500)*q.s := by
      apply le_of_not_gt
      intro vHigh
      apply h.missingRight
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [rightLowerU,rightLowerV,high,vHigh]
    have tUpperU : (22/25)*q.c-q.s<q.loU+q.side := by
      linarith only [a.2.1,cp,sn]
    have tUpperV : -(22/25)*q.s-q.c<q.loV+q.side := by
      linarith only [m.2.2.2,cp,sn]
    have tLowerV : q.loV< -(22/25)*q.s-q.c := by
      linarith only [rightUpperV,h.side,cu,sn]
    have tLowerU : (22/25)*q.c-q.s≤q.loU := by
      apply le_of_not_gt
      intro low
      apply missingT
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,tUpperU,tLowerV,tUpperV]
    linarith only [tLowerU,m.1,m.2.2.2,rightUpperV,cp]
  have fUpperU : (13/50)*q.c-q.s<q.loU+q.side := by
    linarith only [a.2.1,cp,sn]
  have fUpperV : -(13/50)*q.s-q.c<q.loV+q.side := by
    linarith only [m.2.2.2,cp,sn,order]
  have fLowerV : q.loV< -(13/50)*q.s-q.c := by
    linarith only [upperV,h.side,cu,sn]
  have fLowerU : (13/50)*q.c-q.s≤q.loU := by
    apply le_of_not_gt
    intro low
    apply missingF
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,fUpperU,fLowerV,fUpperV]
  have tUpperU : (22/25)*q.c-q.s<q.loU+q.side := by
    linarith only [a.2.1,cp,sn]
  have tUpperV : -(22/25)*q.s-q.c<q.loV+q.side := by
    linarith only [m.2.2.2,cp,sn]
  have tLowerU : q.loU<(22/25)*q.c-q.s := by
    have short := CommonCases.OutwardScalars.increasing_projection q.c q.s
      (103/500) 1 cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
    linarith only [upperU,h.side,short]
  have tLowerV : -(22/25)*q.s-q.c≤q.loV := by
    apply le_of_not_gt
    intro low
    apply missingT
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [tLowerU,tUpperU,low,tUpperV]
  have support := positive_segment q h fLowerU fLowerV fUpperV
    tLowerU tUpperU tLowerV
  have first := mul_nonneg sn (sub_nonneg.mpr upperU)
  have last := mul_nonneg cp.le (sub_nonneg.mpr upperV)
  have length := mul_pos (sub_pos.mpr h.side)
    (show 0<q.c+q.s by linarith only [cp,sn])
  have product := mul_nonneg cp.le sn
  nlinarith only [support,first,last,length,bounds.2.2.2.2,product]

end N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint
