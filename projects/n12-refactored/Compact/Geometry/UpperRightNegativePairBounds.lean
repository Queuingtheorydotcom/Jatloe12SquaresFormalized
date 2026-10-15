import Compact.Geometry.UpperRightNegativeTopBounds
import Compact.Geometry.C977CornerSectorBounds

/-! Three continuous support margins for the negative northeast corner
and negative top square. The second margin uses two coarse estimates of
one coefficient; no finite angle subdivision or numerical certificate is
used. -/
namespace N12Compact.UpperRightNegativePairBounds

open C977CornerCubic C977CornerSectorBounds

theorem plus {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0≤e+f-33/20+(13/20)*f^2+
      e^2*(c+(13/20)*s^2-(1/20)*c*s)+
      e*f*(s-11/10-(1/20)*s^2-(13/20)*c*s) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0≤e := by linarith only [eb.1]
  have ef := mul_nonneg ep en.1
  have chord := mul_nonneg (sub_nonneg.mpr tb.2.1)
    (show 0≤(3/5)*c-2/5 by linarith only [tb.1])
  have defect : 1-c≤(3/5)*s^2 := by
    nlinarith only [chord,tn.2.2]
  have cs := mul_nonneg tn.1 (sub_nonneg.mpr tb.2.1)
  have bBound : 79/80≤c+(13/20)*s^2-(1/20)*c*s := by
    nlinarith only [defect,cs,sq_nonneg (s-1/2)]
  have factor : 0≤1-s/20-(13/20)*c := by
    linarith only [tb.2.1,tb.2.2.2.1]
  have aBound : -(11/10)≤s-11/10-(1/20)*s^2-(13/20)*c*s := by
    have product := mul_nonneg tn.1 factor
    nlinarith only [product]
  have first := mul_nonneg (sq_nonneg e) (sub_nonneg.mpr bBound)
  have last := mul_nonneg ef (sub_nonneg.mpr aBound)
  have arc : 1+(4/5)*e*f≤e+f := by
    have strong := UpperRightNegativeTopBounds.arc en
    nlinarith only [strong,ef]
  have ordered := mul_nonneg ep (sub_nonneg.mpr en.2.1)
  nlinarith only [first,last,arc,ordered,en.2.2,sq_nonneg e]

theorem minus {e f c s : ℝ} (en : Normal e f) (tn : Normal c s)
    (order : e*s≤f*c) :
    0≤e+f-33/20+(13/20)*f^2+
      e^2*(c-s+(13/20)*s^2+(61/100)*c*s)+
      e*f*(c+s-44/25+(61/100)*s^2-(13/20)*c*s) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0≤e := by linarith only [eb.1]
  have cp : 0≤c := by linarith only [tb.1]
  have ef := mul_nonneg ep en.1
  have cs := mul_nonneg cp tn.1
  have arc := UpperRightNegativeTopBounds.arc en
  have topArc := UpperRightNegativeTopBounds.arc tn
  have aBound : -(19/25)≤c+s-44/25+(61/100)*s^2-(13/20)*c*s := by
    nlinarith only [topArc,cs,sq_nonneg s]
  have last := mul_nonneg ef (sub_nonneg.mpr aBound)
  have factor : 0≤1-(63/100)*c-s/50 := by
    linarith only [tb.2.1,tb.2.2.2.1]
  have product := mul_nonneg (sub_nonneg.mpr tn.2.1) factor
  have identity : c-s+(13/20)*s^2+(61/100)*c*s-63/100=
      (c-s)*(1-(63/100)*c-s/50) := by
    linear_combination (63/100)*tn.2.2
  have bBound : 63/100≤c-s+(13/20)*s^2+(61/100)*c*s := by
    linarith only [identity,product]
  by_cases large : 2/5≤f
  · have first := mul_nonneg (sq_nonneg e) (sub_nonneg.mpr bBound)
    have coefficient : 0≤(3/50)*f-e/50 := by
      linarith only [large,eb.2.1]
    have remainder := mul_nonneg ep coefficient
    nlinarith only [first,last,arc,remainder,en.2.2]
  · have small : f≤2/5 := le_of_lt (lt_of_not_ge large)
    have sineOrder : s≤f := sine_order en tn (by linarith only [order])
    have smallSine : s≤2/5 := le_trans sineOrder small
    have cosine : 9/10≤c := by
      have sineSquare := mul_nonneg (sub_nonneg.mpr smallSine)
        (show 0≤2/5+s by linarith only [tn.1])
      by_contra no
      have contrary : c<9/10 := lt_of_not_ge no
      have cosineSquare := mul_nonneg
        (show 0≤9/10-c by linarith only [contrary])
        (show 0≤9/10+c by linarith only [cp])
      nlinarith only [sineSquare,cosineSquare,tn.2.2]
    have crossBound := mul_nonneg tn.1 (sub_nonneg.mpr cosine)
    have stronger : 4/5≤c-s+(13/20)*s^2+(61/100)*c*s := by
      nlinarith only [cosine,crossBound,tn.1,sq_nonneg (s-7/20)]
    have first := mul_nonneg (sq_nonneg e) (sub_nonneg.mpr stronger)
    nlinarith only [first,last,arc,en.2.2,sq_nonneg e,ef]

theorem upper {e f c s : ℝ} (en : Normal e f) (tn : Normal c s)
    (order : e*s≤f*c) :
    0≤e*f*(1-c)+s*(e+f-f^2+e*f*(c-44/25)-e^2*s) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0≤e := by linarith only [eb.1]
  have ef := mul_nonneg ep en.1
  have arc := UpperRightNegativeTopBounds.arc en
  have ordered := mul_nonneg ep (sub_nonneg.mpr en.2.1)
  have core : 0≤e+f-f^2-(44/25)*e*f := by
    nlinarith only [arc,ordered,en.2.2,sq_nonneg e]
  have cross := mul_nonneg ep (sub_nonneg.mpr order)
  have bracket : 0≤e+f-f^2+e*f*(c-44/25)-e^2*s := by
    nlinarith only [core,cross]
  have first := mul_nonneg ef (sub_nonneg.mpr tb.2.1)
  have last := mul_nonneg tn.1 bracket
  linarith only [first,last]

end N12Compact.UpperRightNegativePairBounds
