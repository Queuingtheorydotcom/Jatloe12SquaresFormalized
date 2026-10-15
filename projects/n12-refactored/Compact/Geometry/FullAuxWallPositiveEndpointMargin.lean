import Compact.Geometry.C977CornerSectorBounds

/-! The positive outer square's endpoint comparison when its angle is
no greater than the opposite central angle. A monotone arc and a single
rational disk cover the full sector. -/
namespace N12Compact.FullAuxWallPositiveEndpointMargin

open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

theorem shallow_margin {C S b t : ℝ} (cn : Normal C S) (bn : Normal b t)
    (order : C*t≤S*b) :
    0≤1-b*(1-C+C^2-(2/5)*C*S)+t*(S*(1-C)-(2/5)*C^2) := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have Cp : 0<C := by linarith only [cb.1]
  have bp : 0≤b := by linarith only [bb.1]
  let P := 1-C+C^2-(2/5)*C*S
  let R := (2/5)*C^2-S*(1-C)
  change 0≤1-b*P-t*R
  by_cases small : S≤(2/5)*C
  · have positive := mul_nonneg Cp.le
      (show 0≤C-(2/5)*S by linarith only [cn.1,cn.2.1])
    have pp : 0≤P := by dsimp [P]; nlinarith only [positive,cb.2.1]
    have slopeIdentity : R*C-P*S=(2/5)*C-S := by
      dsimp [P,R]
      linear_combination ((2/5)*C)*cn.2.2
    have slope : P*S≤R*C := by linarith only [slopeIdentity,small]
    have sine : t≤S := sine_order cn bn (by nlinarith only [order])
    have arc := linear_arc_max cn bn sine pp slope
    have endpoint : P*C+R*S=2*C-1 := by
      dsimp [P,R]
      linear_combination (C-1)*cn.2.2
    nlinarith only [arc,endpoint,cb.2.1]
  · have large : (2/5)*C≤S := (lt_of_not_ge small).le
    have range := mul_nonneg
      (show 0≤5*S-2*C by linarith only [large])
      (show 0≤5*S+2*C by linarith only [Cp,cn.1])
    have upper : C≤19/20 := by
      apply le_of_not_gt
      intro bad
      have square := mul_pos (sub_pos.mpr bad)
        (show 0<C+(19/20 : ℝ) by linarith only [Cp])
      nlinarith only [square,range,cn.2.2]
    have deficit := mul_nonneg Cp.le
      (show 0≤1-C-(1/20 : ℝ) by linarith only [upper])
    have cross := mul_nonneg Cp.le
      (show 0≤S-(7/25 : ℝ) by linarith only [large,cb.1])
    have pBound : P≤9/10 := by
      dsimp [P]
      nlinarith only [deficit,cross,cb.1]
    have correction := mul_nonneg cn.1 (sub_nonneg.mpr cb.2.1)
    have rBound : R≤2/5 := by
      dsimp [R]
      nlinarith only [correction,cn.2.2,sq_nonneg S]
    have disk : (9/10)*b+(2/5)*t<1 := by
      nlinarith only [bn.2.2,sq_nonneg (b-9/10),sq_nonneg (t-2/5)]
    have first := mul_nonneg bp (sub_nonneg.mpr pBound)
    have second := mul_nonneg bn.1 (sub_nonneg.mpr rBound)
    nlinarith only [disk,first,second]

#print axioms shallow_margin
end N12Compact.FullAuxWallPositiveEndpointMargin
