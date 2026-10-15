import Compact.Completion.OtherCases.BottomBarSupport

/-! The remaining negative southeast entrance needs only its actual marker
and elbow. The F4 anchor is unnecessary for these full faces, so the same
three-square ending can cover both remaining merged-F5 labels. -/
namespace N12Compact.Completion.OtherCases.NegativeTripleFaces
open S12 S12Pilot
set_option Elab.async false

structure Data (E : OpenSquare) (t : ℝ) : Prop where
  signed : E.s= -t
  cosinePositive : 0<E.c
  sinePositive : 0<t
  ordered : t≤E.c
  sideLarge : 1<E.side
  lowerU : 0≤E.loU
  upperU : 1<E.loU+E.side
  elbowLowerU : E.loU<(13/50)*E.c
  lowerV : E.loV<0
  upperV : E.loV+E.side≤t
  sharpUpperV : E.loV+E.side≤(21/40)*t+(1/8)*E.c
  firstBar : (13/50)*t-E.c≤E.loV
  bar : (4/5)*t-E.c≤E.loV ∨ -1≤ -t*(E.loU+E.side)+E.c*E.loV

theorem faces (E : OpenSquare) (t : ℝ) (signed : E.s= -t)
    (side : 1<E.side) (cp : 0<E.c) (tp : 0<t) (order : t≤E.c)
    (marker : E.Inside (7/20) (-7/20)) (elbow : E.Inside (13/50) 0)
    (missingCenter : ¬E.Inside 0 0) (missingOrigin : ¬E.Inside 1 0)
    (missingSharp : ¬E.Inside (21/40) (1/8))
    (bottom : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬E.Inside x (-1)) : Data E t := by
  have m := marker
  have d := elbow
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,zero_add,
    add_zero,mul_neg] at m d
  have unit : E.c^2+t^2=1 := by simpa only [signed,neg_sq] using E.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds E.c t cp tp.le order unit
  have vLower : E.loV<0 := by linarith only [m.2.2.1,order]
  have uLower : 0≤E.loU := by
    apply le_of_not_gt
    intro low
    apply missingCenter
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add,add_zero]
    refine ⟨low,?_,vLower,?_⟩ <;> linarith only [m.2.1,d.2.2.2,cp,tp]
  have uUpper : 1<E.loU+E.side := by linarith only [uLower,side]
  have rUpperV : E.loV+E.side≤t := by
    apply le_of_not_gt
    intro high
    apply missingOrigin
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one,mul_zero,zero_mul,add_zero]
    refine ⟨?_,?_,?_,high⟩ <;>
      linarith only [d.1,uUpper,vLower,cp,tp,bounds.2.1]
  have yUpperV : E.loV+E.side≤(21/40)*t+(1/8)*E.c := by
    apply le_of_not_gt
    intro high
    apply missingSharp
    simp only [OpenSquare.Inside,InBands,signed,neg_neg]
    refine ⟨?_,?_,?_,by simpa only [mul_comm] using high⟩ <;>
      linarith only [d.1,uUpper,vLower,cp,tp,order,bounds.2.1]
  have bar := BottomBarSupport.negative E t signed side cp tp.le order uLower marker elbow bottom
  exact ⟨signed,cp,tp,order,side,uLower,uUpper,by linarith only [d.1],
    vLower,rUpperV,by linarith only [yUpperV],bar.1,bar.2⟩

#print axioms faces
end N12Compact.Completion.OtherCases.NegativeTripleFaces
