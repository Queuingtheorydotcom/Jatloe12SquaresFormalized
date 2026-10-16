import Compact.Geometry.C977CornerSectorBounds
import Compact.Geometry.UpperRightCornerLongitudinalNorm

/-! Continuous scalar margins for the complete top-wall/corner support
chain. The two broad estimates cover entire arcs, not sampled angles. -/
namespace N12Compact.UpperRightCornerLongitudinalBounds

open C977CornerCubic C977CornerSectorBounds

theorem disk_margin {e f a b : ℝ} (normal : Normal e f)
    (small : a^2+b^2<1) : 0<1-a*e-b*f := by
  have identity : (a*e+b*f)^2+(a*f-b*e)^2=a^2+b^2 := by
    linear_combination (a^2+b^2)*normal.2.2
  nlinarith only [identity,small,sq_nonneg (a*f-b*e),sq_nonneg (a*e+b*f-1)]

/-- The strict top marker controls a shallower test direction. The
one-variable norm certificate covers the entire top-wall canonical arc. -/
theorem marker_margin {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0≤1+e*(c-44/25+(13/50)*s^2-(43/500)*c*s)+
      f*((43/500)*c^2+s-(13/50)*c*s-3/5) := by
  let A := c-44/25+(13/50)*s^2-(43/500)*c*s
  let B := (43/500)*c^2+s-(13/50)*c*s-3/5
  have residual := UpperRightCornerLongitudinalNorm.residual_nonpos tn
  have identity : A^2+B^2-1=
      261/100-(88/25)*c-(6/5)*s+(187949/250000)*c^2+(57/100)*c*s := by
    dsimp [A,B]
    linear_combination (((13/50)*s-(43/500)*c)^2+381/2500)*tn.2.2
  have circle : (e*A+f*B)^2+(e*B-f*A)^2=A^2+B^2 := by
    linear_combination (A^2+B^2)*en.2.2
  change 0≤1+e*A+f*B
  clear_value A B
  nlinarith only [identity,residual,circle,sq_nonneg (e*B-f*A),
    sq_nonneg (e*A+f*B+1)]

private theorem products {c s : ℝ} (normal : Normal c s) :
    s^2≤1/2 ∧ c*s≤1/2 := by
  have bounds := normal_bounds normal
  have order := mul_nonneg (sub_nonneg.mpr normal.2.1)
    (show 0≤c+s by linarith only [bounds.1,normal.1])
  constructor <;> nlinarith only [normal.2.2,order,sq_nonneg (c-s)]

private theorem arc_margin {c s : ℝ} (normal : Normal c s) :
    1+(4/5)*c*s≤c+s := by
  have bounds := normal_bounds normal
  have product := mul_nonneg (sub_nonneg.mpr bounds.2.2.2.2.1)
    (show 0≤3/2-(c+s) by linarith only [bounds.2.2.2.2.2])
  nlinarith only [product,normal.2.2]

/-- The simultaneous lower-U and lower-V faces of T supply this margin
for every steeper positive test direction. -/
theorem lower_pair_margin {e f c s : ℝ}
    (en : Normal e f) (tn : Normal c s) (order : 0≤f*c-e*s) :
    0≤1+e*(c-s-44/25+(61/100)*s^2+(13/20)*c*s)+
      f*(c+s-5/4+(13/20)*s^2-(61/100)*c*s) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have cp : 0<c := by linarith only [tb.1]
  have fs : s≤f := sine_order en tn (by linarith only [order])
  have prod := products tn
  let A := c-s-44/25+(61/100)*s^2+(13/20)*c*s
  let B := c+s-5/4+(13/20)*s^2-(61/100)*c*s
  change 0≤1+e*A+f*B
  by_cases small : s≤2/5
  · have wide : 9/10≤c := by
      have square := mul_nonneg tn.1 (sub_nonneg.mpr small)
      nlinarith only [tn.2.2,square,small,tb.1,sq_nonneg (c-9/10)]
    have mixed := mul_nonneg tn.1 (sub_nonneg.mpr wide)
    have aBound : -(47/50)≤A := by
      dsimp [A]
      nlinarith only [mixed,wide,tn.1,sq_nonneg (s-7/20)]
    have chord := mul_nonneg (sub_nonneg.mpr wide) (sub_nonneg.mpr tb.2.1)
    have defect : 1-c≤(10/19)*s^2 := by
      nlinarith only [chord,tn.2.2]
    have cap := mul_nonneg tn.1 (sub_nonneg.mpr tb.2.1)
    have bBound : -(1/4)≤B := by
      dsimp [B]
      nlinarith only [defect,cap,tn.1,sq_nonneg s]
    have first := mul_nonneg (show 0≤e by linarith only [eb.1])
      (sub_nonneg.mpr aBound)
    have last := mul_nonneg en.1 (sub_nonneg.mpr bBound)
    have disk := disk_margin en (show (47/50 : ℝ)^2+(1/4)^2<1 by norm_num)
    clear_value A B
    nlinarith only [first,last,disk]
  · have large : 2/5≤s := (lt_of_not_ge small).le
    have ap : A≤0 := by
      dsimp [A]
      nlinarith only [tb.2.1,tn.1,prod.1,prod.2]
    have slope : 0≤c*B-s*A := by
      have identity : c*B-s*A=1+(23/20)*s-(5/4)*c := by
        dsimp [A,B]
        linear_combination (1-(61/100)*s)*tn.2.2
      rw [identity]
      nlinarith only [large,tb.2.1]
    have endpoint : 0<1+c*A+s*B := by
      have identity : 1+c*A+s*B=2-(44/25)*c-(3/5)*s := by
        dsimp [A,B]
        linear_combination (1+(13/20)*s)*tn.2.2
      have disk := disk_margin tn (show (22/25 : ℝ)^2+(3/10)^2<1 by norm_num)
      rw [identity]
      linarith only [disk]
    have first := mul_nonneg (neg_nonneg.mpr ap)
      (sub_nonneg.mpr (dot_le_one tn en))
    have last := mul_nonneg (sub_nonneg.mpr fs) slope
    have identity : c*((1+e*A+f*B)-(1+c*A+s*B))=
        -A*(1-(c*e+s*f))+(f-s)*(c*B-s*A) := by
      linear_combination -A*tn.2.2
    have scaled : 0≤c*((1+e*A+f*B)-(1+c*A+s*B)) := by
      rw [identity]
      linarith only [first,last]
    have monotone := nonneg_of_mul_nonneg_right scaled cp
    clear_value A B
    linarith only [monotone,endpoint]

/-- The wing-upper-V face forces a definite top-wall tilt. In shallower
test directions the following complete support margin is nonnegative. -/
theorem upper_pair_margin {e f c s : ℝ}
    (en : Normal e f) (tn : Normal c s) (order : f*c-e*s≤0)
    (tilt : (3/10)*c≤s) :
    0≤1+e*(c+s-23/20-(61/100)*s^2-(13/20)*c*s)+
      f*(s-c+(61/100)*c*s-(13/20)*s^2-3/5) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have fs : f≤s := sine_order tn en (by linarith only [order])
  have prod := products tn
  have arc := arc_margin tn
  let A := c+s-23/20-(61/100)*s^2-(13/20)*c*s
  let B := s-c+(61/100)*c*s-(13/20)*s^2
  have mixed : 0≤c*s := mul_nonneg (by linarith only [tb.1]) tn.1
  have aBound : -(91/200)≤A := by
    dsimp [A]
    nlinarith only [arc,prod.1,mixed]
  have difference : 0≤c-s := sub_nonneg.mpr tn.2.1
  have factor : 0≤1-(61/100)*s := by linarith only [tb.2.2.2.1]
  have positive := mul_nonneg difference factor
  have bIdentity : B=-(c-s)*(1-(61/100)*s)-(1/25)*s^2 := by dsimp [B]; ring
  have bNonpos : B≤0 := by
    rw [bIdentity]
    nlinarith only [positive,sq_nonneg s]
  have gap : c-s≤7/10 := by nlinarith only [tilt,tb.2.1]
  have correction := mul_nonneg difference tn.1
  have bBound : -(18/25)≤B := by
    nlinarith only [bIdentity,gap,correction,prod.1]
  change 0≤1+e*A+f*(B-3/5)
  by_cases small : s≤1/2
  · have square := mul_nonneg tn.1 (sub_nonneg.mpr small)
    have aSmall : -(121/400)≤A := by
      dsimp [A]
      nlinarith only [arc,square,small,mixed]
    have first := mul_nonneg (show 0≤e by linarith only [eb.1])
      (sub_nonneg.mpr aSmall)
    have last := mul_nonneg en.1 (sub_nonneg.mpr bBound)
    clear_value A B
    nlinarith only [first,last,eb.2.1,fs,small]
  · have large : 1/2≤s := (lt_of_not_ge small).le
    have narrow : c≤87/100 := by
      have square := mul_nonneg (sub_nonneg.mpr large) tn.1
      nlinarith only [tn.2.2,square,large,tb.1,sq_nonneg (c-87/100)]
    have gapSmall : c-s≤37/100 := by linarith only [narrow,large]
    have factorSmall : 1-(61/100)*s≤139/200 := by linarith only [large]
    have first := mul_nonneg factor (sub_nonneg.mpr gapSmall)
    have last := mul_nonneg (show 0≤(37/100 : ℝ) by norm_num)
      (sub_nonneg.mpr factorSmall)
    have bSmall : -(7/25)≤B := by
      nlinarith only [bIdentity,first,last,prod.1]
    have aWeight := mul_nonneg (show 0≤e by linarith only [eb.1])
      (sub_nonneg.mpr aBound)
    have bWeight := mul_nonneg en.1 (sub_nonneg.mpr bSmall)
    have disk := disk_margin en (show (91/200 : ℝ)^2+(22/25)^2<1 by norm_num)
    clear_value A B
    nlinarith only [aWeight,bWeight,disk]

#print axioms lower_pair_margin
#print axioms upper_pair_margin
#print axioms marker_margin
end N12Compact.UpperRightCornerLongitudinalBounds
