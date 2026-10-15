import Compact.Geometry.UpperRightNegativePairLongitudinalBounds

noncomputable section

/-! A negative southeast neighbor sharpens the positive central owner's
upper support through either genuine incoming axis. All estimates are
continuous on the canonical arcs. -/
namespace N12Compact.CentralNegativeNeighborBounds

open C977CornerCubic UpperRightCornerLongitudinalBounds

def excess (C S c t : ℝ) : ℝ :=
  c-1+(7/20)*t+t*(1-C)+
    S*(-c+(7/20)*(c+t)*C+(7/20)*(c-t)*S)

theorem small_of_positive {C S c t : ℝ} (an : Normal C S) (bn : Normal c t)
    (positive : 0<excess C S c t) : S<2/5 := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have cp : 0≤c := by linarith only [bb.1]
  have defect := UpperRightNegativePairLongitudinalBounds.cosine_defect an
  have first := mul_nonneg bn.1 (sub_nonneg.mpr defect)
  have sumBound : (7/20)*(C+S)≤1/2 := by linarith only [ab.2.2.2.2.2]
  have mixedBound : (7/20)*C+S/4≤11/25 := by
    have square : ((7/20)*C+S/4)^2≤37/200 := by
      nlinarith only [an.2.2,sq_nonneg (C/4-(7/20)*S)]
    nlinarith only [square,sq_nonneg ((7/20)*C+S/4-11/25)]
  have cWeight := mul_nonneg cp (sub_nonneg.mpr sumBound)
  have tWeight := mul_nonneg bn.1 (sub_nonneg.mpr mixedBound)
  have coefficient : (7/20)*(c+t)*C+((7/20)*c+t/4)*S≤c/2+(11/25)*t := by
    nlinarith only [cWeight,tWeight]
  have last := mul_nonneg an.1 (sub_nonneg.mpr coefficient)
  have bound : excess C S c t≤c-1+(7/20)*t+S*(-c/2+(11/25)*t) := by
    dsimp [excess]; nlinarith only [first,last]
  by_contra no
  have large : 2/5≤S := le_of_not_gt no
  have negative : 0≤c/2-(11/25)*t := by linarith only [bn.2.1,cp]
  have replace := mul_nonneg (sub_nonneg.mpr large) negative
  have disk := disk_margin bn (show (4/5 : ℝ)^2+(263/500)^2<1 by norm_num)
  nlinarith only [positive,bound,replace,disk]

theorem upper_bound {C S c t : ℝ} (an : Normal C S) (bn : Normal c t)
    (small : S≤2/5) : excess C S c t≤(9/100)*C*(C*c-S*t) := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have cp : 0≤c := by linarith only [bb.1]
  have defect := UpperRightNegativePairLongitudinalBounds.cosine_defect an
  have first := mul_nonneg bn.1 (sub_nonneg.mpr defect)
  have p1 : 0≤(7/20)*c+(11/25)*t :=
    add_nonneg (mul_nonneg (by norm_num) cp) (mul_nonneg (by norm_num) bn.1)
  have p2 : 0≤(11/25)*c+t/4 :=
    add_nonneg (mul_nonneg (by norm_num) cp) (div_nonneg bn.1 (by norm_num))
  have cWeight := mul_nonneg p1 (sub_nonneg.mpr ab.2.1)
  have sWeight := mul_nonneg p2 (sub_nonneg.mpr small)
  have coefficient : -c+((7/20)*c+(11/25)*t)*C+((11/25)*c+t/4)*S≤
      -(237/500)*c+(27/50)*t := by nlinarith only [cWeight,sWeight]
  have last := mul_nonneg an.1 (sub_nonneg.mpr coefficient)
  have identity : excess C S c t-(9/100)*C*(C*c-S*t)=
      (91/100)*c-1+(7/20)*t+t*(1-C)+
      S*(-c+((7/20)*c+(11/25)*t)*C+((11/25)*c-(7/20)*t)*S) := by
    dsimp [excess]
    linear_combination (-(9/100)*c)*an.2.2
  have bound : excess C S c t-(9/100)*C*(C*c-S*t)≤
      (91/100)*c-1+(7/20)*t+S*(-(237/500)*c+(27/50)*t) := by
    nlinarith only [identity,first,last]
  by_cases sign : -(237/500)*c+(27/50)*t≤0
  · have product := mul_nonneg an.1 (neg_nonneg.mpr sign)
    have disk := disk_margin bn (show (91/100 : ℝ)^2+(7/20)^2<1 by norm_num)
    nlinarith only [bound,product,disk]
  · have product := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤-(237/500)*c+(27/50)*t by linarith only [sign])
    have disk := disk_margin bn (show (1801/2500 : ℝ)^2+(283/500)^2<1 by norm_num)
    nlinarith only [bound,product,disk]

theorem own_coefficients {c t : ℝ} (bn : Normal c t) :
    (1-c)*(1-t)≤4/45 ∧ 1/2≤c-t+t^2 := by
  have b := normal_bounds bn
  have defect := UpperRightNegativePairLongitudinalBounds.cosine_defect bn
  have first := mul_nonneg (sub_nonneg.mpr b.2.2.2.1) (sub_nonneg.mpr defect)
  have cubic := mul_nonneg (sq_nonneg (t-2/3))
    (show 0≤t+1/3 by linarith only [bn.1])
  have last := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤1-(c+t)/2 by linarith only [b.2.2.2.2.2])
  constructor
  · nlinarith only [first,cubic]
  · nlinarith only [last,bn.2.2]

end N12Compact.CentralNegativeNeighborBounds
