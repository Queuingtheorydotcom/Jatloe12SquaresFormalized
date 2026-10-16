import Compact.Geometry.FullAuxWallRightSupport

/-! A shared small-offset consequence of the genuine right-wall
clearance and the actual opposite-square support projection. -/
namespace N12Compact.FullAuxWallSmallOffset
open C977CornerCubic
set_option Elab.async false

theorem cosine {C S : ℝ} (dn : Normal C S) (slope : 25*S≤9*C) :
    47/50<C := by
  have bounds := normal_bounds dn
  have cp : 0≤C := by linarith only [bounds.1]
  have first := mul_nonneg (sub_nonneg.mpr slope)
    (show 0≤9*C+25*S by linarith only [cp,dn.1])
  apply lt_of_not_ge
  intro small
  have second := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤47/50+C by linarith only [cp])
  nlinarith only [first,second,dn.2.2]

/-- The denominator bound uses the already proved opposite-angle
restriction, rather than the much weaker whole-quadrant cosine bound. -/
theorem offset {c s C S e u : ℝ} (an : Normal c s) (dn : Normal C S)
    (narrow : 4*s≤c) (slope : 25*S≤9*C)
    (small : e<1/1250) (projected : (c*C+s*S)*u≤e) : u<1/1000 := by
  have ab := FullAuxWallRightMargin.central_bounds an narrow
  have dc := cosine dn slope
  have cp : 0≤C := by linarith only [dc]
  have first := mul_nonneg (sub_nonneg.mpr ab.1) cp
  have second := mul_nonneg an.1 dn.1
  have alpha : 564/625≤c*C+s*S := by nlinarith only [first,second,dc]
  apply lt_of_not_ge
  intro large
  have weighted := mul_nonneg
    (show 0≤c*C+s*S by linarith only [alpha]) (sub_nonneg.mpr large)
  nlinarith only [projected,small,weighted,alpha]

#print axioms offset
end N12Compact.FullAuxWallSmallOffset
