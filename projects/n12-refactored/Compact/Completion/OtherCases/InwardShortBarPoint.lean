import Compact.Completion.OtherCases.LowerCornerSupport
import Compact.Completion.CommonCases.CanonicalScalars
import Compact.Geometry.ClosedFrames

/-! A short genuine bottom segment completes the inward central triangle.
The positive sector uses its exact lower-vertex support; the opposite
sector follows from three strict projection margins. -/
namespace N12Compact.Completion.OtherCases.InwardShortBarPoint
open S12 S12Pilot
set_option Elab.async false

private theorem positive (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20)) (elbow : q.Inside (13/50) 0)
    (inner : q.Inside 0 (-13/50)) (missingF : ¬q.Inside 1 (-13/50))
    (avoid : ∀ x : ℝ,13/50≤x → x≤7/20 → ¬q.Inside x (-1)) :
    q.Inside (1/20) (-1/20) := by
  by_contra missing
  have bounds := CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal
  have cu := bounds.2.1
  have kLowU : q.loU<q.c*(1/20)+q.s*(-1/20) := by
    linarith only [inner.1,cp,sn]
  have kHighU : q.c*(1/20)+q.s*(-1/20)<q.loU+q.side := by
    linarith only [marker.2.1,order]
  have kLowV : q.loV< -q.s*(1/20)+q.c*(-1/20) := by
    linarith only [marker.2.2.1,cp,sn]
  have upperV : q.loV+q.side≤ -(1/20)*(q.c+q.s) := by
    apply le_of_not_gt
    intro high
    exact missing ⟨kLowU,kHighU,kLowV,by linarith only [high]⟩
  have fLowU : q.loU<q.c-q.s*(13/50) := by
    linarith only [marker.1,cp,sn]
  have fHighV : -q.s-q.c*(13/50)<q.loV+q.side := by
    linarith only [inner.2.2.2,sn]
  have fShort := (short_projections q (21/100) (19/20) (by norm_num)).2.1
  have fLowV : q.loV< -q.s-q.c*(13/50) := by
    linarith only [upperV,side,fShort]
  have upperU : q.loU+q.side≤q.c-q.s*(13/50) := by
    apply le_of_not_gt
    intro high
    exact missingF (by
      simpa only [OpenSquare.Inside,InBands,mul_one] using
        And.intro fLowU (And.intro high (And.intro fLowV fHighV)))
  have rHighU : q.c*(13/50)-q.s<q.loU+q.side := by
    linarith only [elbow.2.1,sn]
  have rHighV : -q.s*(13/50)-q.c<q.loV+q.side := by
    linarith only [marker.2.2.2,cp,order]
  have rShort := (short_projections q (19/20) (21/100) (by norm_num)).2.1
  have rLowV : q.loV< -q.s*(13/50)-q.c := by
    linarith only [upperV,side,rShort]
  have lowerU : q.c*(13/50)-q.s≤q.loU := by
    apply le_of_not_gt
    intro low
    exact avoid (13/50) le_rfl (by norm_num) (by
      simpa only [OpenSquare.Inside,InBands,mul_neg,neg_mul,mul_one] using
        And.intro low (And.intro rHighU (And.intro rLowV rHighV)))
  have sp : 0<q.s := by linarith only [lowerU,upperU,side,cu]
  have tShort := (short_projections q (13/20) (37/50) (by norm_num)).2.1
  have tLowU : q.loU<q.c*(7/20)-q.s := by
    linarith only [upperU,side,tShort]
  have tHighU : q.c*(7/20)-q.s<q.loU+q.side := by
    linarith only [lowerU,side,cu]
  have tHighV : -q.s*(7/20)-q.c<q.loV+q.side := by
    linarith only [marker.2.2.2,cp]
  have lowerV : -q.s*(7/20)-q.c≤q.loV := by
    apply le_of_not_gt
    intro low
    exact avoid (7/20) (by norm_num) le_rfl (by
      simpa only [OpenSquare.Inside,InBands,mul_neg,neg_mul,mul_one] using
        And.intro tLowU (And.intro tHighU (And.intro low tHighV)))
  have support := LowerCornerSupport.horizontal q (13/50) (7/20) (by norm_num)
    lowerU ⟨rLowV,rHighV⟩ ⟨tLowU,tHighU⟩ lowerV avoid
  have first := mul_nonneg sn (sub_nonneg.mpr upperU)
  have last := mul_nonneg cp.le (sub_nonneg.mpr upperV)
  have extra := mul_pos (sub_pos.mpr side)
    (show 0<q.c+q.s by linarith only [cp,sn])
  have defect := mul_nonneg sn (sub_nonneg.mpr cu)
  have square := sq_nonneg (q.s-5/14)
  have margin : 0<1/20-(3/20)*q.c*q.s+(21/100)*q.s^2 := by
    nlinarith only [defect,square]
  nlinarith only [support,first,last,extra,margin,bounds.2.2.2.2,q.unit_normal]

private theorem negative (q : OpenSquare) (t : ℝ) (signed : q.s= -t)
    (side : 1<q.side) (cp : 0<q.c) (tn : 0≤t) (order : t≤q.c)
    (marker : q.Inside (7/20) (-7/20)) (elbow : q.Inside (13/50) 0)
    (inner : q.Inside 0 (-13/50)) (missingF : ¬q.Inside 1 (-13/50))
    (missingT : ¬q.Inside (7/20) (-1)) : q.Inside (1/20) (-1/20) := by
  by_contra missing
  have m := marker
  have d := elbow
  have p := inner
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,add_zero,zero_add]
    at m d p
  have kHighU : q.c*(1/20)+t*(1/20)<q.loU+q.side := by
    linarith only [m.2.1,cp,tn]
  have kLowV : q.loV<t*(1/20)-q.c*(1/20) := by
    linarith only [p.2.2.1,cp,tn]
  have kHighV : t*(1/20)-q.c*(1/20)<q.loV+q.side := by
    linarith only [d.2.2.2,cp,tn]
  have lowerU : (1/20)*(q.c+t)≤q.loU := by
    apply le_of_not_gt
    intro low
    exact missing (by
      simp only [OpenSquare.Inside,InBands,signed,neg_neg]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,kHighU,kLowV,kHighV])
  have fLowU : q.loU<q.c+t*(13/50) := by linarith only [m.1,cp,tn]
  have fLowV : q.loV<t-q.c*(13/50) := by linarith only [p.2.2.1,tn]
  have short := (short_projections q (19/20) (-(21/100)) (by norm_num)).2.1
  rw [signed] at short
  have fHighU : q.c+t*(13/50)<q.loU+q.side := by
    nlinarith only [lowerU,side,short]
  have upperV : q.loV+q.side≤t-q.c*(13/50) := by
    apply le_of_not_gt
    intro high
    exact missingF (by
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [fLowU,fHighU,fLowV,high])
  have tLowU : q.loU<q.c*(7/20)+t := by linarith only [m.1,tn]
  have tHighV : t*(7/20)-q.c<q.loV+q.side := by linarith only [m.2.2.2,cp]
  have tShort := (short_projections q (37/50) (-(13/20)) (by norm_num)).2.1
  rw [signed] at tShort
  have tLowV : q.loV<t*(7/20)-q.c := by
    nlinarith only [upperV,side,tShort]
  have upperU : q.loU+q.side≤q.c*(7/20)+t := by
    apply le_of_not_gt
    intro high
    exact missingT (by
      simp only [OpenSquare.Inside,InBands,signed,neg_neg]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [tLowU,high,tLowV,tHighV])
  have finalShort := (short_projections q (3/10) (-(19/20)) (by norm_num)).2.1
  rw [signed] at finalShort
  nlinarith only [lowerU,upperU,side,finalShort]

theorem point (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (-7/20)) (elbow : q.Inside (13/50) 0)
    (inner : q.Inside 0 (-13/50)) (missingF : ¬q.Inside 1 (-13/50))
    (avoid : ∀ x : ℝ,13/50≤x → x≤7/20 → ¬q.Inside x (-1)) :
    q.Inside (1/20) (-1/20) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have m := (same _ _).mpr marker
  have d := (same _ _).mpr elbow
  have p := (same _ _).mpr inner
  have missing' : ¬r.Inside 1 (-13/50) := fun h => missingF ((same _ _).mp h)
  have avoid' : ∀ x : ℝ,13/50≤x → x≤7/20 → ¬r.Inside x (-1) :=
    fun x low high own => avoid x low high ((same _ _).mp own)
  have side' : 1<r.side := by simpa only [shape] using side
  have bounds := abs_le.mp range
  apply (same _ _).mp
  by_cases sign : 0≤r.s
  · exact positive r side' cp sign bounds.2 m d p missing' avoid'
  · exact negative r (-r.s) (by ring) side' cp (by linarith only [sign])
      (by linarith only [bounds.1]) m d p missing' (avoid' (7/20) (by norm_num) le_rfl)

#print axioms point
end N12Compact.Completion.OtherCases.InwardShortBarPoint

