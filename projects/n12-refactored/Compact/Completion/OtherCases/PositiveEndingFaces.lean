import Compact.Completion.OtherCases.BottomBarSupport
import Compact.Completion.OtherCases.PositiveEndingScalars

/-! True full faces and a strictly owned point for the final positive
southeast owner. F4 ownership and F4 exclusion are both unrestricted. -/
namespace N12Compact.Completion.OtherCases.PositiveEndingFaces
open S12 S12Pilot
open C1092WallProfileScalars
set_option Elab.async false

structure Data (E : OpenSquare) : Prop where
  cosineLarge : 113/125<E.c
  cosineUpper : E.c≤1
  sinePositive : 0<E.s
  sineSmall : E.s<43/100
  ordered : E.s≤E.c
  sideLarge : 1<E.side
  upperU : E.loU+E.side≤E.c
  upperUPositive : 0<E.loU+E.side
  halfPositive : 0<half E.c E.s
  halfSmall : half E.c E.s<9/40
  lowerPoint : E.Inside 0 (-half E.c E.s)
  bar : -(13/50)*E.s-E.c≤E.loV ∨ -1≤E.s*E.loU+E.c*E.loV

theorem faces (E : OpenSquare) (side : 1<E.side)
    (cp : 0<E.c) (sp : 0<E.s) (order : E.s≤E.c)
    (marker : E.Inside (7/20) (-7/20)) (elbow : E.Inside (13/50) 0)
    (outer : E.Inside 1 (-13/50))
    (missingOrigin : ¬E.Inside 1 0) (missingSharp : ¬E.Inside (21/40) (1/8))
    (avoid : ∀ x : ℝ,13/50≤x → x≤4/5 → ¬E.Inside x (-1)) : Data E := by
  have bounds := CommonCases.CanonicalScalars.bounds E.c E.s cp sp.le order E.unit_normal
  have cu := bounds.2.1
  have upperU : E.loU+E.side≤E.c := by
    apply le_of_not_gt
    intro high
    apply missingOrigin
    simp only [OpenSquare.Inside,InBands,mul_one,mul_zero,add_zero]
    refine ⟨?_,high,?_,?_⟩ <;>
      linarith only [elbow.1,outer.2.2.1,elbow.2.2.2,cp,sp]
  have upperV : E.loV+E.side≤(1/8)*E.c-(21/40)*E.s := by
    apply le_of_not_gt
    intro high
    apply missingSharp
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [elbow.1,outer.2.1,marker.2.2.1,high,cp,sp,order]
  have slope : 53*E.s<25*E.c := by linarith only [elbow.2.2.2,upperV]
  have square := mul_pos (show 0<25*E.c-53*E.s by linarith only [slope])
    (show 0<25*E.c+53*E.s by linarith only [cp,sp])
  have cosineLarge : 113/125<E.c := by
    by_contra bad
    have low : E.c≤113/125 := le_of_not_gt bad
    have bound := mul_nonneg (sub_nonneg.mpr low)
      (show 0≤113/125+E.c by linarith only [cp])
    nlinarith only [square,E.unit_normal,bound]
  have sineSmall : E.s<43/100 := by
    by_contra bad
    have high : 43/100≤E.s := le_of_not_gt bad
    have bound := mul_nonneg (sub_nonneg.mpr high)
      (show 0≤E.s+43/100 by linarith only [sp])
    nlinarith only [square,E.unit_normal,bound]
  let z := half E.c E.s
  have quarter := quarter_data E.c E.s cp.le sp.le E.unit_normal
  have zp : 0<z := div_pos sp (by linarith only [cp])
  have zu : z<9/40 := by
    have scaled := mul_pos (show 0<1+z^2 by positivity) (sub_pos.mpr slope)
    have relation : 0<25*(1-z^2)-106*z := by
      nlinarith only [scaled,quarter.2.2.2.1,quarter.2.2.2.2]
    by_contra bad
    have high : 9/40≤z := le_of_not_gt bad
    have square := mul_nonneg (sub_nonneg.mpr high)
      (show 0≤z+9/40 by linarith only [zp])
    nlinarith only [relation,square,high]
  have defect : E.s*z=1-E.c := by
    dsimp only [z,half]
    field_simp [show (1+E.c)≠0 by linarith only [cp]]
    nlinarith only [E.unit_normal]
  have zLowerU : E.loU< -E.s*z := by linarith only [upperU,side,defect]
  have zUpperU : -E.s*z<E.loU+E.side := by
    linarith only [elbow.2.1,cp,cu,defect]
  have extra := mul_nonneg zp.le (sub_nonneg.mpr cu)
  have zLowerV : E.loV< -E.c*z := by
    nlinarith only [marker.2.2.1,extra,zu,bounds.2.2.1]
  have margin := mul_pos zp
    (show 0<E.c-(13/50)*(1+E.c) by linarith only [cosineLarge])
  have relation := congrArg (fun x : ℝ => (13/50)*x) quarter.2.2.1
  have zUpperV : -E.c*z<E.loV+E.side := by
    nlinarith only [elbow.2.2.2,margin,relation]
  have point : E.Inside 0 (-z) := by
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add,mul_neg,neg_mul] using
      And.intro zLowerU (And.intro zUpperU (And.intro zLowerV zUpperV))
  have lastLowU : E.loU<(4/5)*E.c-E.s := by
    linarith only [marker.1,slope,cp]
  exact ⟨cosineLarge,cu,sp,sineSmall,order,side,upperU,
    by linarith only [outer.2.1,cp,order],zp,zu,point,
    BottomBarSupport.positive E side cp sp.le cu elbow lastLowU avoid⟩

#print axioms faces
end N12Compact.Completion.OtherCases.PositiveEndingFaces
