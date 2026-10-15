import Compact.Completion.OtherCases.OrdinaryLeftTop.Inputs
import Compact.Completion.OtherCases.OrdinaryLeftTop.ScalarMargins

/-! ORDINARY-LEFT-TOP-OBSTRUCTION.md, sections 1.2 and 1.3: the actual
positive frame, both strict angle endpoints, four weak face bounds and
the two strict upper points. No wall or foreign-owner identification is used.
Source translation only; compiler acceptance is deliberately deferred. -/
namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop
open S12 S12Pilot
set_option Elab.async false

structure Profile (q : OpenSquare) : Prop where
  cosine : 0 < q.c
  sine : 0 < q.s
  canonical : q.s ≤ q.c
  angleLower : (2/3)*q.c < q.s
  angleUpper : q.s < (8/11)*q.c
  lowerU : -(43/500)*q.c ≤ q.loU
  lowerV : -(27/100)*q.s-(1/25)*q.c ≤ q.loV
  upperU : q.loU+q.side ≤ (11/25)*q.c+q.s
  upperV : q.loV+q.side ≤ q.c

theorem positive_profile (q : OpenSquare) (h : Input q)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c) : Profile q := by
  have unit := q.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds q.c q.s cp sn order unit
  have cu : q.c ≤ 1 := bounds.2.1
  have m := h.marker
  have a := h.anchor
  have middleLowerV : -(1/2)*q.s ≤ q.loV := by
    apply le_of_not_gt
    intro low
    apply h.middle
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.1,a.2.2.2,m.2.1,cp,sn,order,low]
  have cornerUpperV : q.loV+q.side ≤ q.c := by
    apply le_of_not_gt
    intro high
    apply h.corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.1,a.2.2.1,m.2.1,cp,sn,order,high]
  have topFarUpperU : q.loU+q.side ≤ (37/50)*q.c+q.s := by
    apply le_of_not_gt
    intro high
    have topFarUpperV : -(37/50)*q.s+q.c < q.loV+q.side := by
      linarith only [middleLowerV,h.side,cu,sn]
    apply h.topFar
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.1,m.2.2.1,cp,sn,order,high,topFarUpperV]
  have leftLowerU : -(43/500)*q.c ≤ q.loU := by
    apply le_of_not_gt
    intro low
    have leftLowerV : q.loV < (43/500)*q.s := by
      linarith only [cornerUpperV,h.side,cu,sn]
    apply h.left
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,leftLowerV,a.2.1,a.2.2.2,cp,sn,order]
  have sixth : (1/6)*q.c < q.s := by
    apply lt_of_not_ge
    intro no
    have projection := ScalarMargins.lowSixth q.c q.s cp sn order unit
      (by linarith only [no])
    linarith only [leftLowerU,topFarUpperU,h.side,projection]
  have shortProjection := ScalarMargins.sixthSlopeSine q.c q.s cp sn order unit
    (by linarith only [sixth])
  have topNearUpperU : q.loU+q.side ≤ (11/25)*q.c+q.s := by
    apply le_of_not_gt
    intro high
    have topNearUpperV : -(11/25)*q.s+q.c < q.loV+q.side := by
      linarith only [middleLowerV,h.side,shortProjection]
    apply h.topNear
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.1,m.2.2.1,cp,sn,order,high,topNearUpperV]
  have angleLower : (2/3)*q.c < q.s := by
    apply lt_of_not_ge
    intro no
    have projection := ScalarMargins.lowTwoThirds q.c q.s cp sn order unit no
    linarith only [leftLowerU,topNearUpperU,h.side,projection]
  have lowerLowerV : -(27/100)*q.s-(1/25)*q.c ≤ q.loV := by
    apply le_of_not_gt
    intro low
    have lowerLowerU : q.loU < (27/100)*q.c-(1/25)*q.s := by
      apply lt_of_not_ge
      intro no
      have projection := ScalarMargins.seventeenOneOhFour q.c q.s cp sn order unit
      linarith only [no,topNearUpperU,h.side,projection]
    apply h.lower
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [lowerLowerU,low,m.2.1,a.2.2.2,cp,sn]
  have angleUpper : q.s < (8/11)*q.c := by
    apply lt_of_not_ge
    intro no
    have projection := ScalarMargins.highEightElevenths q.c q.s cp sn order unit no
    linarith only [lowerLowerV,cornerUpperV,h.side,projection]
  exact ⟨cp,by linarith only [angleLower,cp],order,angleLower,angleUpper,
    leftLowerU,lowerLowerV,topNearUpperU,cornerUpperV⟩

/-- The same four band estimates work for every parameter between the two
points used by the chapter; the published endpoints are recorded below. -/
theorem upper_point (q : OpenSquare) (h : Input q) (p : Profile q)
    (x : ℝ) (lo : 7/25 ≤ x) (hi : x ≤ 2/5) : q.Inside x 1 := by
  have sn : 0 ≤ q.s := p.sine.le
  have upperU := ScalarMargins.pointUpperU q.c q.s p.cosine sn p.canonical
    q.unit_normal p.angleUpper.le
  have upperV := ScalarMargins.pointUpperV q.c q.s p.cosine sn p.canonical
    q.unit_normal p.angleLower.le
  have xnonnegative : 0 ≤ x := le_trans (by norm_num) lo
  have xCosine := mul_nonneg p.cosine.le (sub_nonneg.mpr lo)
  have xSine := mul_nonneg sn (sub_nonneg.mpr hi)
  have uBound : q.c*x+q.s ≤ (2/5)*q.c+q.s :=
    add_le_add_right (by nlinarith only [mul_nonneg p.cosine.le (sub_nonneg.mpr hi)]) _
  have vBound : -q.s*x+q.c ≤ -(7/25)*q.s+q.c := by
    nlinarith only [mul_nonneg sn (sub_nonneg.mpr lo)]
  have lowerU : q.loU < q.c*x+q.s := by
    have step := mul_nonneg p.cosine.le xnonnegative
    linarith only [h.anchor.1,step,p.sine]
  have lowerV : q.loV < -q.s*x+q.c := by
    have canonicalTerm := mul_nonneg (by norm_num : (0:ℝ)≤2/5)
      (sub_nonneg.mpr p.canonical)
    linarith only [h.anchor.2.2.1,xSine,canonicalTerm,p.cosine]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [mul_one] using lowerU
  · have bound : q.c*x+q.s < q.loU+q.side := by
      linarith only [uBound,p.lowerU,upperU,h.side]
    simpa only [mul_one] using bound
  · simpa only [mul_one] using lowerV
  · have bound : -q.s*x+q.c < q.loV+q.side := by
      linarith only [vBound,p.lowerV,upperV,h.side]
    simpa only [mul_one] using bound

theorem upper_points (q : OpenSquare) (h : Input q) (p : Profile q) :
    q.Inside (7/25) 1 ∧ q.Inside (2/5) 1 :=
  ⟨upper_point q h p _ (by norm_num) (by norm_num),
    upper_point q h p _ (by norm_num) (by norm_num)⟩

end N12Compact.Completion.OtherCases.OrdinaryLeftTop
