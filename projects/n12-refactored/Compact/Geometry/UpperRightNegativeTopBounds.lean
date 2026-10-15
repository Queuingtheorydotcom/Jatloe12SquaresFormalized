import Compact.Geometry.UpperRightCornerLongitudinalBounds

/-! Continuous margins for a positive northeast corner and a negative
top square. The true top boundary is retained in the two scaled margins. -/
namespace N12Compact.UpperRightNegativeTopBounds

open C977CornerCubic UpperRightCornerLongitudinalBounds

theorem arc {c s : ℝ} (normal : Normal c s) :
    1+(41/50)*c*s≤c+s := by
  have b := normal_bounds normal
  have product := mul_nonneg (sub_nonneg.mpr b.2.2.2.2.1)
    (show 0≤1-(41/100)*(c+s+1) by linarith only [b.2.2.2.2.2])
  nlinarith only [product,normal.2.2]

private theorem products {c s : ℝ} (normal : Normal c s) :
    0≤c*s ∧ c*s≤1/2 ∧ s≤5/7 := by
  have b := normal_bounds normal
  exact ⟨mul_nonneg (by linarith only [b.1]) normal.1,
    by nlinarith only [normal.2.2,sq_nonneg (c-s)],
    by linarith only [normal.2.1,b.2.2.2.2.2]⟩

theorem forward_lower {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0≤1+e*(c+s-44/25+(61/100)*s^2-(13/20)*c*s)+
      f*(c-s-5/4+(13/20)*s^2+(61/100)*c*s) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have cs := products tn
  have ar := arc tn
  have aBound : -(19/25)≤c+s-44/25+(61/100)*s^2-(13/20)*c*s := by
    nlinarith only [ar,cs.1,sq_nonneg s]
  have factor : 0≤1-(63/100)*c-s/50 := by
    linarith only [tb.2.1,tb.2.2.2.1]
  have product := mul_nonneg (sub_nonneg.mpr tn.2.1) factor
  have identity : c-s-5/4+(13/20)*s^2+(61/100)*c*s+31/50=
      (c-s)*(1-(63/100)*c-s/50) := by
    linear_combination (63/100)*tn.2.2
  have first := mul_nonneg (show 0≤e by linarith only [eb.1])
    (sub_nonneg.mpr aBound)
  have last := mul_nonneg en.1 (show 0≤c-s-5/4+(13/20)*s^2+
      (61/100)*c*s+31/50 by linarith only [identity,product])
  have disk := disk_margin en (show (19/25 : ℝ)^2+(31/50)^2<1 by norm_num)
  nlinarith only [first,last,disk]

theorem forward_upper {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0≤s+e*(1-c-(44/25)*s+c*s)+f*((2/5)*s-s^2) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have cs := products tn
  have first := mul_nonneg (sub_nonneg.mpr tb.2.1)
    (show 0≤1-s by linarith only [tb.2.2.2.1])
  have last := mul_nonneg tn.1 (show 0≤5/7-s by linarith only [cs.2.2])
  have ew := mul_nonneg (show 0≤e by linarith only [eb.1]) first
  have fw := mul_nonneg en.1 last
  have disk := disk_margin en (show (19/25 : ℝ)^2+(11/35)^2<1 by norm_num)
  have base := mul_nonneg tn.1 disk.le
  nlinarith only [ew,fw,base]

private theorem coefficients {e f : ℝ} (en : Normal e f) :
    -(19/25)≤e+f-63/50-e^2/2-(3/5)*e*f ∧
    -(1/20)≤e-f-(3/5)*e^2+e*f/2 := by
  have b := normal_bounds en
  have ef := products en
  have ar := arc en
  constructor
  · nlinarith only [ar,ef.1,en.2.2,sq_nonneg f]
  · have product := mul_nonneg (sub_nonneg.mpr en.2.1)
      (show 0≤1-(3/5)*e by linarith only [b.2.1])
    nlinarith only [product,ef.2.1]

theorem reverse_lower_upper {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0≤1+c*(e+f-63/50-e^2/2-(3/5)*e*f)+
      s*(e-f-(3/5)*e^2+e*f/2) := by
  have tb := normal_bounds tn
  have co := coefficients en
  have first := mul_nonneg (show 0≤c by linarith only [tb.1])
    (sub_nonneg.mpr co.1)
  have last := mul_nonneg tn.1 (sub_nonneg.mpr co.2)
  have disk := disk_margin tn (show (19/25 : ℝ)^2+(1/20)^2<1 by norm_num)
  nlinarith only [first,last,disk]

theorem reverse_upper_upper {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0≤c+s-1+s*(c*(e+f-63/50-e^2/2-(3/5)*e*f)+
      s*(e-f-(3/5)*e^2+e*f/2)) := by
  have tb := normal_bounds tn
  have co := coefficients en
  have cs := products tn
  have first := mul_nonneg cs.1 (sub_nonneg.mpr co.1)
  have last := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr co.2)
  have ar := arc tn
  have ordered := mul_nonneg tn.1 (sub_nonneg.mpr tn.2.1)
  nlinarith only [first,last,ar,ordered,cs.1]

theorem reverse_lower_lower {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0≤c*(1-e)*(1-f)+f*(1-(19/25)*c)+s*f*(1-f) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have first := mul_nonneg (mul_nonneg (show 0≤c by linarith only [tb.1])
    (sub_nonneg.mpr eb.2.1)) (show 0≤1-f by linarith only [eb.2.2.2.1])
  have middle := mul_nonneg en.1 (show 0≤1-(19/25)*c by linarith only [tb.2.1])
  have last := mul_nonneg (mul_nonneg tn.1 en.1)
    (show 0≤1-f by linarith only [eb.2.2.2.1])
  linarith only [first,middle,last]

theorem reverse_upper_lower {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0≤c*f*(1-c)+s*c*(1-e)*(1-f)+s*f*(1-s*f-(19/25)*c) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ef := products en
  have product := mul_nonneg (sub_nonneg.mpr tb.2.1)
    (show 0≤(3/5)*c-2/5 by linarith only [tb.1])
  have defect : (2/5)*s^2≤c*(1-c) := by
    nlinarith only [product,tn.2.2]
  have capped := mul_nonneg (sq_nonneg s) (show 0≤5/7-f by linarith only [ef.2.2])
  have disk := disk_margin tn (show (19/25 : ℝ)^2+(11/35)^2<1 by norm_num)
  have base := mul_nonneg tn.1 disk.le
  have coefficient : 0≤c*(1-c)+s*(1-s*f-(19/25)*c) := by
    nlinarith only [defect,capped,base]
  have first := mul_nonneg en.1 coefficient
  have last := mul_nonneg
    (mul_nonneg (mul_nonneg tn.1 (show 0≤c by linarith only [tb.1]))
      (sub_nonneg.mpr eb.2.1))
    (show 0≤1-f by linarith only [eb.2.2.2.1])
  nlinarith only [first,last]

end N12Compact.UpperRightNegativeTopBounds
