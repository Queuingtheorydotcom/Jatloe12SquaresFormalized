import Compact.Geometry.C977CornerSectorBounds

/-! The lower relative-angle branch of the remaining genuine left-square
support inequality. A diagonal comparison handles the whole arc, with
no angle enumeration or numerical certificate. -/
namespace N12Compact.FullAuxWallPositiveLeftBelowMargin
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

theorem margin {l r C S u : ℝ}
    (ln : Normal l r) (dn : Normal C S)
    (large : 4/25≤r) (small : S≤11/50)
    (nonnegative : 0≤u) (offset : u≤1/1000)
    (order : r*C-l*S≤0) :
    2-(543/500)*r^2-l*(1+(l*C+r*S))+
      l*(r*C-l*S)*(1-C+(2/5)*S)+l*(l*C+r*S)*u≤0 := by
  have lb := normal_bounds ln
  have db := normal_bounds dn
  have lp : 0<l := by linarith only [lb.1]
  have cp : 0<C := by linarith only [db.1]
  have sine := sine_order dn ln (by linarith only [order])
  have cosine := cosine_order dn ln sine
  have square := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤11/50+S by linarith only [dn.1])
  have cLower : 97/100≤C := by
    apply le_of_not_gt
    intro wrong
    have factor := mul_nonneg (sub_nonneg.mpr wrong.le)
      (show 0≤97/100+C by linarith only [cp])
    nlinarith only [square,factor,dn.2.2]
  have lLower : 97/100≤l := le_trans cLower cosine
  let alpha := l*C+r*S
  let k := l*S-r*C
  let D := 1-C+(2/5)*S
  let diagonal := 2-(543/500)*r^2-2*l+l*u
  have ap : 0≤alpha := by
    exact add_nonneg (mul_nonneg lp.le cp.le) (mul_nonneg ln.1 dn.1)
  have au : alpha≤1 := dot_le_one ln dn
  have kp : 0≤k := by dsimp [k]; linarith only [order]
  have first := mul_nonneg cp.le (sub_nonneg.mpr large)
  have second := mul_nonneg dn.1 (sub_nonneg.mpr lb.2.1)
  have kBound : k≤(2/5)*S := by
    dsimp [k]
    nlinarith only [first,second,cLower,small]
  have kD : k≤D := by dsimp [D]; linarith only [kBound,db.2.1]
  have unit : alpha^2+k^2=1 := by
    dsimp [alpha,k]
    calc
      _ = (l^2+r^2)*(C^2+S^2) := by ring
      _ = 1 := by rw [ln.2.2,dn.2.2]; norm_num
  have defectProduct := mul_nonneg ap (sub_nonneg.mpr au)
  have defect : 1-alpha≤k^2 := by nlinarith only [unit,defectProduct]
  have comparison := mul_nonneg kp (sub_nonneg.mpr kD)
  have weighted := mul_nonneg lp.le
    (show 0≤k*D-(1-alpha) by nlinarith only [defect,comparison])
  have correction := mul_nonneg
    (mul_nonneg lp.le (sub_nonneg.mpr au)) nonnegative
  have identity :
      (2-(543/500)*r^2-l*(1+(l*C+r*S))+
        l*(r*C-l*S)*(1-C+(2/5)*S)+l*(l*C+r*S)*u)-diagonal=
      l*((1-alpha)-k*D)-l*(1-alpha)*u := by
    dsimp [diagonal,alpha,k,D]; ring
  have domination :
      2-(543/500)*r^2-l*(1+(l*C+r*S))+
        l*(r*C-l*S)*(1-C+(2/5)*S)+l*(l*C+r*S)*u≤diagonal := by
    clear_value alpha k D diagonal
    nlinarith only [identity,weighted,correction]
  have rSquare := mul_nonneg (sub_nonneg.mpr large)
    (show 0≤r+4/25 by linarith only [ln.1])
  have coefficient := mul_nonneg (sq_nonneg r)
    (show 0≤(543/500)*(1+l)-2-13/100 by linarith only [lLower])
  have sideFactor : 0≤l*(1+l) := mul_nonneg lp.le (by linarith only [lp])
  have weightedOffset := mul_nonneg sideFactor (sub_nonneg.mpr offset)
  have width := mul_nonneg (sub_nonneg.mpr lb.2.1)
    (show 0≤l+2 by linarith only [lp])
  have diagonalIdentity : (1+l)*diagonal=
      r^2*(2-(543/500)*(1+l))+l*(1+l)*u := by
    dsimp [diagonal]
    linear_combination -2*ln.2.2
  have scaled : (1+l)*diagonal<0 := by
    clear_value diagonal
    nlinarith only [diagonalIdentity,rSquare,coefficient,weightedOffset,width]
  have negative : diagonal<0 := neg_of_mul_neg_right scaled
    (show 0≤1+l by linarith only [lp])
  clear_value diagonal
  linarith only [domination,negative]

#print axioms margin
end N12Compact.FullAuxWallPositiveLeftBelowMargin
