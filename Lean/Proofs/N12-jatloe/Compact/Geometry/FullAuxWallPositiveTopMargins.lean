import Compact.Geometry.FullAuxWallPositiveEndpointMargin

/-! Support margins for the actual top endpoint. All canonical angles
are covered, retaining both relative-angle signs of each SAT selector. -/
namespace N12Compact.FullAuxWallPositiveTopMargins
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

private theorem defect {b t : ℝ} (bn : Normal b t) : 1-b≤(3/5)*t^2 := by
  have bb := normal_bounds bn
  have product := mul_nonneg (sub_nonneg.mpr bb.2.1)
    (show 0≤3*b-2 by linarith only [bb.1])
  nlinarith only [product,bn.2.2]

theorem c_axis_below {C S b t : ℝ} (cn : Normal C S) (bn : Normal b t)
    (order : C*t≤S*b) :
    C*(2-b-(13/20)*t^2+(1/20)*b*t)+
      S*(-(1/20)+(1/20)*t^2+(13/20)*b*t-t)≤1 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  let f := 2-b-(13/20)*t^2+(1/20)*b*t
  let g := -(1/20)+(1/20)*t^2+(13/20)*b*t-t
  have tp := bn.1
  have bp : 0≤b := by linarith only [bb.1]
  have cross := mul_nonneg bp tp
  have fp : 0≤f := by
    dsimp [f]
    nlinarith only [bb.2.1,bn.2.2,sq_nonneg b,cross]
  have product := mul_nonneg tp (sub_nonneg.mpr bb.2.1)
  have gn : g≤0 := by
    dsimp [g]
    nlinarith only [bn.2.2,sq_nonneg b,product,tp]
  have sine : t≤S := sine_order cn bn (by nlinarith only [order])
  have cosine : C≤b := cosine_order cn bn sine
  have first := mul_nonneg fp (sub_nonneg.mpr cosine)
  have second := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr sine) gn
  have endpoint : b*f+t*g=2*b-1 := by
    dsimp [f,g]
    linear_combination ((1/20)*t-1)*bn.2.2
  change C*f+S*g≤1
  nlinarith only [first,second,endpoint,bb.2.1]

theorem c_axis_above {C S b t : ℝ} (cn : Normal C S) (bn : Normal b t)
    (order : S*b≤C*t) :
    C*(2-b-(37/50)*t^2-(3/5)*b*t)+
      S*((3/5)-(3/5)*t^2+(37/50)*b*t-t)≤1 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  let f := 2-b-(37/50)*t^2-(3/5)*b*t
  let g := (3/5)-(3/5)*t^2+(37/50)*b*t-t
  have bp : 0<b := by linarith only [bb.1]
  have square : t^2≤1/2 := by
    have p := mul_nonneg (sub_nonneg.mpr bn.2.1)
      (show 0≤b+t by linarith only [bp,bn.1])
    nlinarith only [p,bn.2.2]
  have cross : b*t≤1/2 := by nlinarith only [bn.2.2,sq_nonneg (b-t)]
  have fp : 0≤f := by dsimp [f]; nlinarith only [square,cross,bb.2.1]
  by_cases small : 21*t≤10*b
  · have slopeIdentity : g*b-f*t=(3/5)*b-(63/50)*t := by
      dsimp [f,g]
      linear_combination ((37/50)*t)*bn.2.2
    have slope : f*t≤g*b := by
      clear_value f g
      linarith only [slopeIdentity,small]
    have sine : S≤t := sine_order bn cn (by nlinarith only [order])
    have arc := linear_arc_max bn cn sine fp slope
    have endpoint : b*f+t*g=2*b-1 := by
      dsimp [f,g]
      linear_combination (-(3/5)*t-1)*bn.2.2
    change C*f+S*g≤1
    nlinarith only [arc,endpoint,bb.2.1]
  · have large : 10*b≤21*t := (lt_of_not_ge small).le
    have range := mul_nonneg (sub_nonneg.mpr large)
      (show 0≤21*t+10*b by linarith only [bp,bn.1])
    have lower : (2/5 : ℝ)≤t := by
      apply le_of_not_gt
      intro bad
      have square := mul_pos (sub_pos.mpr bad)
        (show 0<(2/5 : ℝ)+t by linarith only [bn.1])
      nlinarith only [square,range,bn.2.2]
    have tSquare := mul_nonneg (sub_nonneg.mpr lower)
      (show 0≤t+(2/5 : ℝ) by linarith only [bn.1])
    have bt1 := mul_nonneg bn.1 (sub_nonneg.mpr bb.1)
    have bt2 := mul_nonneg (show (0:ℝ)≤7/10 by norm_num)
      (sub_nonneg.mpr lower)
    have fBound : f≤81/100 := by
      dsimp [f]
      nlinarith only [defect bn,tSquare,bt1,bt2]
    have gProduct := mul_nonneg bn.1 (sub_nonneg.mpr bb.2.1)
    have gBound : g≤1/2 := by
      dsimp [g]
      nlinarith only [gProduct,lower,sq_nonneg t]
    have first := mul_nonneg (show 0≤C by linarith only [cb.1])
      (sub_nonneg.mpr fBound)
    have second := mul_nonneg cn.1 (sub_nonneg.mpr gBound)
    have disk : (81/100)*C+(1/2)*S<1 := by
      nlinarith only [cn.2.2,sq_nonneg (C-81/100),sq_nonneg (S-1/2)]
    change C*f+S*g≤1
    clear_value f g
    nlinarith only [first,second,disk]

theorem b_axis_above {C S b t : ℝ} (cn : Normal C S) (bn : Normal b t)
    (order : S*b≤C*t) :
    0≤1+b*(C-2+S^2+(2/5)*C*S-(9/10)*S)+
      t*(S-C*S-(2/5)*C^2+(9/10)*C) := by
  have cb := normal_bounds cn
  let F := 1-C+C^2-(2/5)*C*S+(9/10)*S
  let G := S*(1-C)+C*((9/10)-(2/5)*C)
  have Cp : 0≤C := by linarith only [cb.1]
  have fp1 := mul_nonneg cn.1
    (show 0≤(9/10 : ℝ)-(2/5)*C by linarith only [cb.2.1])
  have fp : 0≤F := by dsimp [F]; nlinarith only [fp1,cb.2.1,sq_nonneg C]
  have gp1 := mul_nonneg cn.1 (sub_nonneg.mpr cb.2.1)
  have gp2 := mul_nonneg Cp
    (show 0≤(9/10 : ℝ)-(2/5)*C by linarith only [cb.2.1])
  have gp : 0≤G := by dsimp [G]; linarith only [gp1,gp2]
  have sine : S≤t := sine_order bn cn (by nlinarith only [order])
  have cosine : b≤C := cosine_order bn cn sine
  have first := mul_nonneg fp (sub_nonneg.mpr cosine)
  have second := mul_nonneg gp (sub_nonneg.mpr sine)
  have endpoint : 1-C*F+S*G=2*(1-C) := by
    dsimp [F,G]
    linear_combination (1-C)*cn.2.2
  have identity : 1+b*(C-2+S^2+(2/5)*C*S-(9/10)*S)+
      t*(S-C*S-(2/5)*C^2+(9/10)*C)=1-b*F+t*G := by
    dsimp [F,G]
    linear_combination b*cn.2.2
  clear_value F G
  nlinarith only [first,second,endpoint,identity,cb.2.1]

#print axioms c_axis_below
#print axioms c_axis_above
#print axioms b_axis_above
end N12Compact.FullAuxWallPositiveTopMargins
