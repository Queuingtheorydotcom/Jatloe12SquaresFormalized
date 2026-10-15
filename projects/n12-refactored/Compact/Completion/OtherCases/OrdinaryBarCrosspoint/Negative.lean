import Compact.Completion.OtherCases.OrdinaryBarCrosspoint.Inputs
import Compact.Completion.OtherCases.OrdinaryBarCrosspoint.Scalars

/-! ORDINARY-BAR-CROSSPOINT.md sections 2--3. The missing lower-u
alternative uses both complete sides of the slope 1/2 comparison. The other
alternative uses the full foreign segment and its actual closed vertex. -/
namespace N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint
open S12 S12Pilot
set_option Elab.async false

private theorem negative_bands (q : OpenSquare) (t : ℝ) (signed : q.s= -t)
    (x y : ℝ) : q.Inside x y ↔
      q.loU<q.c*x-t*y ∧ q.c*x-t*y<q.loU+q.side ∧
      q.loV<t*x+q.c*y ∧ t*x+q.c*y<q.loV+q.side := by
  simp only [OpenSquare.Inside,InBands,signed,neg_mul,neg_neg,sub_eq_add_neg]

theorem negative_lower_impossible (q : OpenSquare) (h : Input q) (t : ℝ)
    (signed : q.s= -t) (cp : 0<q.c) (tn : 0≤t) (order : t≤q.c)
    (lowerU : q.c/2≤q.loU) : False := by
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have cu := (CommonCases.CanonicalScalars.bounds q.c t cp tn order unit).2.1
  have bands := negative_bands q t signed
  have m := (bands _ _).mp h.marker
  have a := (bands _ _).mp h.near
  have missingT := h.segment (22/25) (by norm_num) le_rfl
  have rightLowerU : q.loU<(543/500)*q.c := by
    linarith only [m.1,cp,order]
  have rightLowerV : q.loV<(543/500)*t := by
    linarith only [a.2.2.1,cp,tn]
  have rightUpperU : (543/500)*q.c<q.loU+q.side := by
    linarith only [lowerU,h.side,cu]
  have upperV : q.loV+q.side≤(543/500)*t := by
    apply le_of_not_gt
    intro high
    apply h.missingRight
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [rightLowerU,rightUpperU,rightLowerV,high]
  have hLowerU : q.loU<(543/500)*q.c+t := by
    linarith only [m.1,cp,tn]
  have hLowerV : q.loV<(543/500)*t-q.c := by
    linarith only [upperV,h.side,cu]
  have hUpperV : (543/500)*t-q.c<q.loV+q.side := by
    linarith only [a.2.2.2,cp,order]
  have upperU : q.loU+q.side≤(543/500)*q.c+t := by
    apply le_of_not_gt
    intro high
    apply h.missingLower
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [hLowerU,high,hLowerV,hUpperV]
  have steep : q.c<2*t := by
    apply lt_of_not_ge
    intro shallow
    have short := Scalars.before_half q.c t cp tn unit shallow
    linarith only [upperU,lowerU,h.side,short]
  have tLowerU : q.loU<(22/25)*q.c+t := by
    linarith only [m.1,cp,tn]
  have tUpperU : (22/25)*q.c+t<q.loU+q.side := by
    have short := CommonCases.OutwardScalars.increasing_projection q.c t
      (19/50) 1 cp tn order unit (by norm_num) (by norm_num) (by norm_num)
    linarith only [lowerU,h.side,short]
  have tUpperV : (22/25)*t-q.c<q.loV+q.side := by
    linarith only [a.2.2.2,cp,tn]
  have lowerV : (22/25)*t-q.c≤q.loV := by
    apply le_of_not_gt
    intro low
    apply missingT
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [tLowerU,tUpperU,low,tUpperV]
  have short := Scalars.after_half q.c t cp tn unit steep.le
  linarith only [upperV,lowerV,h.side,short]

theorem negative_upper_impossible (q : OpenSquare) (h : Input q) (t : ℝ)
    (signed : q.s= -t) (cp : 0<q.c) (tn : 0≤t) (order : t≤q.c)
    (upperV : q.loV+q.side≤t/2) : False := by
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have cu := (CommonCases.CanonicalScalars.bounds q.c t cp tn order unit).2.1
  have bands := negative_bands q t signed
  have m := (bands _ _).mp h.marker
  have a := (bands _ _).mp h.near
  have b := (bands _ _).mp h.far
  have missingF := h.segment (13/50) le_rfl (by norm_num)
  have missingT := h.segment (22/25) (by norm_num) le_rfl
  have tLowerU : q.loU<(22/25)*q.c+t := by
    linarith only [m.1,cp,tn]
  have tLowerV : q.loV<(22/25)*t-q.c := by
    linarith only [upperV,h.side,cu,tn]
  have tUpperV : (22/25)*t-q.c<q.loV+q.side := by
    linarith only [a.2.2.2,cp,tn]
  have tUpperU : q.loU+q.side≤(22/25)*q.c+t := by
    apply le_of_not_gt
    intro high
    apply missingT
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [tLowerU,high,tLowerV,tUpperV]
  have fUpperU : (13/50)*q.c+t<q.loU+q.side := by
    linarith only [a.2.1,order]
  have fUpperV : (13/50)*t-q.c<q.loV+q.side := by
    linarith only [b.2.2.2,cp,tn]
  have fLowerU : q.loU<(13/50)*q.c+t := by
    linarith only [tUpperU,h.side,cu]
  have fLowerV : (13/50)*t-q.c≤q.loV := by
    apply le_of_not_gt
    intro low
    apply missingF
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [fLowerU,fUpperU,low,fUpperV]
  have support := negative_segment q h t signed fLowerU fUpperU fLowerV
    tUpperU tLowerV tUpperV
  have first := mul_nonneg tn (sub_nonneg.mpr a.2.1.le)
  have last := mul_nonneg cp.le (sub_nonneg.mpr upperV)
  have length := mul_pos cp (sub_pos.mpr h.side)
  have vertex := Scalars.lower_vertex q.c t cp tn order unit
  nlinarith only [support,first,last,length,vertex]

theorem negative (q : OpenSquare) (h : Input q) (t : ℝ)
    (signed : q.s= -t) (cp : 0<q.c) (tn : 0≤t) (order : t≤q.c) :
    q.Inside (1/2) 0 := by
  by_contra missing
  by_cases lowerU : q.c/2≤q.loU
  · exact negative_lower_impossible q h t signed cp tn order lowerU
  · have bands := negative_bands q t signed
    have m := (bands _ _).mp h.marker
    have a := (bands _ _).mp h.near
    have targetLowerU : q.loU<q.c/2 := lt_of_not_ge lowerU
    have targetUpperU : q.c/2<q.loU+q.side := by
      linarith only [a.2.1,cp,tn]
    have targetLowerV : q.loV<t/2 := by
      linarith only [m.2.2.1,cp,tn]
    have upperV : q.loV+q.side≤t/2 := by
      apply le_of_not_gt
      intro high
      apply missing
      apply (bands _ _).mpr
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [targetLowerU,targetUpperU,targetLowerV,high]
    exact negative_upper_impossible q h t signed cp tn order upperV

end N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint
