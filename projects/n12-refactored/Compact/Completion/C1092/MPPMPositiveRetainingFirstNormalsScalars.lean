import Compact.Geometry.C977CornerCubic

/-! Exact unit-circle margins for POSITIVE-RETAINING-FIRST-NORMALS.
The two derivative comparisons in the supplied proof are replaced by
nonnegative products on the same full closed canonical intervals. -/
namespace N12Compact.C1092MPPMPositiveRetainingFirstNormals
open C977CornerCubic
set_option Elab.async false

theorem sine_small {c s : ℝ} (cn : Normal c s) : s<71/100 := by
  have bounds := normal_bounds cn
  have compare := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤c+s by linarith only [bounds.1,cn.1])
  by_contra no
  have large := mul_nonneg (show 0≤s-71/100 by linarith only [no])
    (show 0≤s+71/100 by linarith only [cn.1])
  nlinarith only [compare,large,cn.2.2]

theorem relative {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    0<c*d+s*t ∧ c*d+s*t≤1 := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have first := mul_pos (show 0<c by linarith only [cb.1])
    (show 0<d by linarith only [eb.1])
  have last := mul_nonneg cn.1 en.1
  have unit : (c*d+s*t)^2+(c*t-s*d)^2=1 := by
    calc
      _ = (c^2+s^2)*(d^2+t^2) := by ring
      _ = 1 := by rw [cn.2.2,en.2.2]; norm_num
  constructor
  · linarith only [first,last]
  · nlinarith only [unit,sq_nonneg (c*t-s*d),sq_nonneg (c*d+s*t-1)]

theorem transverse_base {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    s+(13/50)*(c*d+s*t)*d<1 := by
  have cb := sine_small cn
  have eb := normal_bounds en
  have rel := relative cn en
  have product := mul_le_mul_of_nonneg_right rel.2
    (show 0≤d by linarith only [eb.1])
  nlinarith only [cb,product,eb.2.1]

/-- The first coefficient is at most -.24 by a circle identity; the
second is at most 1/8. These uniform bounds retain both diagonal endpoints. -/
theorem successor_up {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    (c*d+s*t)*(s-1)+(c*t-s*d)*(c+s-1)+(13/50)*d<0 := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  have coefficient := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤1-(c+s)/2 by linarith only [cb.2.2.2.2.2])
  have first : 13/50-c+s-s^2≤-6/25 := by
    nlinarith only [coefficient,cn.2.2]
  have square := mul_nonneg
    (show 0≤3/2-c-s by linarith only [cb.2.2.2.2.2])
    (show 0≤c+s-1/2 by linarith only [cb.2.2.2.2.1])
  have second : (1-c)*(1-s)≤1/8 := by
    nlinarith only [square,cn.2.2]
  have bound1 := mul_le_mul_of_nonneg_left first dp.le
  have bound2 := mul_le_mul_of_nonneg_left second en.1
  have identity :
      (c*d+s*t)*(s-1)+(c*t-s*d)*(c+s-1)+(13/50)*d =
        d*(13/50-c+s-s^2)+t*((1-c)*(1-s)) := by
    calc
      _ = d*(13/50-c+s-s^2)+t*((1-c)*(1-s))+t*(c^2+s^2-1) := by ring
      _ = _ := by rw [cn.2.2]; ring
  rw [identity]
  nlinarith only [bound1,bound2,en.2.1,dp]

/-- Multiplying by positive c avoids division in the opposite angle
order. The cross coefficient is nonpositive, including an equal angle. -/
theorem successor_down {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (order : c*t-s*d≤0) :
    (c*d+s*t)*(s-1)+(c*t-s*d)+(13/50)*d<0 := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cp : 0<c := by linarith only [cb.1]
  have dp : 0<d := by linarith only [eb.1]
  have small := sine_small cn
  have base : 13/50*c-1+s<0 := by linarith only [small,cb.2.1]
  have coefficient : 0≤c+s^2-s := by
    nlinarith only [cb.1,sq_nonneg (s-1/2)]
  have product := mul_nonpos_of_nonpos_of_nonneg order coefficient
  have negative := mul_neg_of_pos_of_neg dp base
  have identity :
      c*((c*d+s*t)*(s-1)+(c*t-s*d)+(13/50)*d) =
        d*(13/50*c-1+s)+(c*t-s*d)*(c+s^2-s) := by
    calc
      _ = d*(13/50*c-1+s)+(c*t-s*d)*(c+s^2-s)+
          d*(s-1)*(c^2+s^2-1) := by ring
      _ = _ := by rw [cn.2.2]; ring
  apply lt_of_not_ge
  intro no
  have nonnegative := mul_nonneg cp.le no
  rw [identity] at nonnegative
  linarith only [nonnegative,negative,product]

#print axioms successor_up
#print axioms successor_down
end N12Compact.C1092MPPMPositiveRetainingFirstNormals
