import Compact.Geometry.C977CornerCubic

/-! Continuous margins for an elbow owning the outer top auxiliary.
The parameters remain the genuine two square orientations. -/
namespace N12Compact.DiagonalOuterElbowBounds
open C977CornerCubic
set_option Elab.async false

theorem shallow_u {c s d t : ℝ} (an : Normal c s) (rn : Normal d t) :
    0<d*(c-2/5+(7/20)*s^2-(7/20)*c*s)+
      t*(13/20-s+(7/20)*s^2+(7/20)*c*s) := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have dp : 0<d := by linarith only [rb.1]
  have cross : c*s≤1/2 := by nlinarith only [an.2.2,sq_nonneg (c-s)]
  have first : 0<c-2/5+(7/20)*s^2-(7/20)*c*s := by
    nlinarith only [ab.1,cross,sq_nonneg s]
  have product := mul_nonneg an.1
    (show 0≤c+s-1 by linarith only [ab.2.2.2.2.1])
  have last : 0≤13/20-s+(7/20)*s^2+(7/20)*c*s := by
    nlinarith only [product,ab.2.2.2.1]
  have positive := mul_pos dp first
  have nonnegative := mul_nonneg rn.1 last
  linarith only [positive,nonnegative]

theorem shallow_v {c s d t : ℝ} (an : Normal c s) (rn : Normal d t) :
    0<d*(c-3/4+(7/10)*s^2)+t*(13/20-s+(7/10)*c*s) := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have dp : 0<d := by linarith only [rb.1]
  have product := mul_nonneg (sub_nonneg.mpr ab.2.1)
    (show 0≤(7/10)*c-3/10 by linarith only [ab.1])
  have first : 0<c-3/4+(7/10)*s^2 := by
    nlinarith only [product,an.2.2]
  have other := mul_nonneg an.1 (sub_nonneg.mpr ab.1)
  have last : 0≤13/20-s+(7/10)*c*s := by
    nlinarith only [other,ab.2.2.2.1]
  have positive := mul_pos dp first
  have nonnegative := mul_nonneg rn.1 last
  linarith only [positive,nonnegative]

theorem wall_coefficients {d t : ℝ} (rn : Normal d t) (narrow : 2*t≤d) :
    2/5+(343/500)*t^2-d*t≤2/5 ∧ t^2+(343/500)*d*t≤3/5 := by
  have rb := normal_bounds rn
  have first := mul_nonneg rn.1 (sub_nonneg.mpr narrow)
  have square := mul_nonneg (sub_nonneg.mpr narrow)
    (show 0≤d+2*t by linarith only [rb.1,rn.1])
  have sine : t^2≤1/5 := by nlinarith only [square,rn.2.2]
  have cross : d*t≤1/2 := by nlinarith only [rn.2.2,sq_nonneg (d-t)]
  exact ⟨by nlinarith only [first,sq_nonneg t],
    by nlinarith only [sine,cross]⟩

theorem shallow_incoming {c s d t : ℝ} (an : Normal c s) (rn : Normal d t)
    (narrow : 2*t≤d) :
    c*(2/5+(343/500)*t^2-d*t)+s*(t^2+(343/500)*d*t)<1 := by
  have ab := normal_bounds an
  have bound := wall_coefficients rn narrow
  have cp : 0≤c := by linarith only [ab.1]
  have first := mul_nonneg cp (sub_nonneg.mpr bound.1)
  have last := mul_nonneg an.1 (sub_nonneg.mpr bound.2)
  nlinarith only [first,last,ab.2.2.2.2.2,cp]

theorem steep {c s d t : ℝ} (an : Normal s c) (rn : Normal d t) :
    0<d*(s-(13/25)*s^2-7/50)+t*c*(1-(13/25)*s) := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have dp : 0<d := by linarith only [rb.1]
  have sp : 0≤s := by linarith only [ab.1]
  have product := mul_nonneg sp (sub_nonneg.mpr ab.2.1)
  have first : 0<s-(13/25)*s^2-7/50 := by
    nlinarith only [product,ab.1]
  have last : 0≤t*c*(1-(13/25)*s) := mul_nonneg
    (mul_nonneg rn.1 an.1) (by linarith only [ab.2.1])
  have positive := mul_pos dp first
  linarith only [positive,last]

end N12Compact.DiagonalOuterElbowBounds
