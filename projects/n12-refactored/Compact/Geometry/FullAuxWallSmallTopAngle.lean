import Compact.Geometry.C977CornerCubic

/-! A continuous bound for the surviving outer-central angle. The two
actual separators and a genuine corner cap suffice; no wall angle or
subdivision of the canonical arc is needed. -/
namespace N12Compact.FullAuxWallSmallTopAngle

open C977CornerCubic
set_option Elab.async false

theorem small_top_angle {a c s C S b t u v : ℝ}
    (an : Normal c s) (cn : Normal C S) (bn : Normal b t)
    (side : 1<a) (sp : 0<s) (aNarrow : 4*s≤c) (cNarrow : 4*S≤C)
    (up : 0<u) (vp : 0<v)
    (cut : (c*C-s*S)*u+(c*S+s*C)*v<(13/50)*s)
    (cap : a*(1+(t*C+b*S))+(b*C-t*S)*v≤b+t+(t*C+b*S)*u) :
    t<3/10 := by
  have ab := normal_bounds an
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0<c := by linarith only [ab.1]
  have Cp : 0<C := by linarith only [cb.1]
  have bp : 0<b := by linarith only [bb.1]
  have range := mul_nonneg (sub_nonneg.mpr cNarrow)
    (show 0≤C+4*S by linarith only [Cp,cn.1])
  have cosine : (9/10 : ℝ)≤C := by
    apply le_of_not_gt
    intro bad
    have square := mul_pos (sub_pos.mpr bad)
      (show 0<(9/10 : ℝ)+C by linarith only [Cp])
    nlinarith only [square,range,cn.2.2]
  have slope1 := mul_nonneg cn.1 (sub_nonneg.mpr aNarrow)
  have slope2 := mul_nonneg cp.le (sub_nonneg.mpr cNarrow)
  have alphaBase : (15/16)*c*C≤c*C-s*S := by
    nlinarith only [slope1,slope2]
  have cosineWeight := mul_nonneg cp.le (sub_nonneg.mpr cosine)
  have alpha : (27/32)*c≤c*C-s*S := by
    nlinarith only [alphaBase,cosineWeight]
  have alphaPositive : 0<c*C-s*S := by nlinarith only [alpha,cp]
  have kNonnegative : 0≤c*S+s*C :=
    add_nonneg (mul_nonneg cp.le cn.1) (mul_nonneg an.1 Cp.le)
  have uSmall : u<(2/25 : ℝ) := by
    apply lt_of_not_ge
    intro large
    have weighted := mul_nonneg alphaPositive.le (sub_nonneg.mpr large)
    have remaining := mul_nonneg kNonnegative vp.le
    nlinarith only [weighted,remaining,alpha,cut,aNarrow,cp]
  let k := t*C+b*S
  have kp : 0≤k := add_nonneg (mul_nonneg bn.1 Cp.le)
    (mul_nonneg bp.le cn.1)
  have order1 := mul_nonneg bn.1
    (show 0≤C+S-1 by linarith only [cb.2.2.2.2.1])
  have order2 := mul_nonneg cn.1 (sub_nonneg.mpr bn.2.1)
  have order : t≤k := by dsimp [k]; nlinarith only [order1,order2]
  have upper1 := mul_nonneg bn.1 (sub_nonneg.mpr cb.2.1)
  have upper2 := mul_nonneg cn.1 (sub_nonneg.mpr bb.2.1)
  have upper : k≤t+1/4 := by
    dsimp [k]
    nlinarith only [upper1,upper2,cNarrow,cb.2.1]
  have alphaB1 := mul_nonneg Cp.le (sub_nonneg.mpr bn.2.1)
  have alphaB2 := mul_nonneg bn.1 (sub_nonneg.mpr cn.2.1)
  have alphaB : 0≤b*C-t*S := by nlinarith only [alphaB1,alphaB2]
  have sideWeight := mul_pos (sub_pos.mpr side)
    (show 0<1+k by linarith only [kp])
  have faceWeight := mul_nonneg alphaB vp.le
  have deficit : 1-b<k*u := by
    change a*(1+k)+(b*C-t*S)*v≤b+t+k*u at cap
    nlinarith only [sideWeight,faceWeight,cap,order]
  have deficitSmall : 1-b<(2/25)*(t+1/4) := by
    calc
      _ < k*u := deficit
      _ ≤ (t+1/4)*u := mul_le_mul_of_nonneg_right upper up.le
      _ < (t+1/4)*(2/25) := mul_lt_mul_of_pos_left uSmall
        (by linarith only [bn.1])
      _ = _ := by ring
  have radial := sq_nonneg (1-b)
  have halfSquare : t^2/2≤1-b := by nlinarith only [radial,bn.2.2]
  apply lt_of_not_ge
  intro large
  have interval := mul_nonneg bn.1 (sub_nonneg.mpr large)
  nlinarith only [interval,large,halfSquare,deficitSmall]

#print axioms small_top_angle
end N12Compact.FullAuxWallSmallTopAngle
