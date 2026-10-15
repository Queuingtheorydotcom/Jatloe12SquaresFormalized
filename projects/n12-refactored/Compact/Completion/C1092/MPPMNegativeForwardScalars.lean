import Compact.Completion.C1092.WallProfileScalars
import Compact.Geometry.C977CornerCubic

/-! Exact all-angle scalar estimates for NEGATIVE-FORWARD-POSITIVE-H,
sections 3 and 5. The successor's complete nonnegative canonical sector
is retained. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMNegativeForward
open S12 S12Pilot C977CornerCubic C1092WallProfileScalars
set_option Elab.async false

theorem source_angle {c s : ℝ} (cn : Normal c s) (width : 1<c+(13/50)*s) :
    0<s ∧ 87/100<c ∧ s<49/100 ∧ c<1 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have sp : 0<s := by linarith only [width,cb.2.1]
  let x := half c s
  have data := quarter_data c s cp.le cn.1 cn.2.2
  have xp : 0<x := div_pos sp (by linarith only [cp])
  have cosine : (1+x^2)*c=1-x^2 := data.2.2.2.1
  have sine : (1+x^2)*s=2*x := data.2.2.2.2
  have identity : (1+x^2)*(c+(13/50)*s-1)=2*x*(13/50-x) := by
    linear_combination cosine+(13/50)*sine
  have scaled := mul_pos (show 0<1+x^2 by positivity)
    (show 0<c+(13/50)*s-1 by linarith only [width])
  have small : x<13/50 := by
    apply lt_of_not_ge
    intro high
    have bad := mul_nonpos_of_nonneg_of_nonpos xp.le
      (show 13/50-x≤0 by linarith only [high])
    nlinarith only [identity,scaled,bad]
  have square := mul_pos (show 0<13/50-x by linarith only [small])
    (show 0<13/50+x by linarith only [xp])
  have close : 87/100<c := by
    apply lt_of_not_ge
    intro low
    have bad := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1+x^2 by positivity) (show c-87/100≤0 by linarith only [low])
    nlinarith only [bad,cosine,square]
  have narrow : s<49/100 := by
    have product := mul_pos (show 0<13/50-x by linarith only [small])
      (show 0<2-(49/100)*(x+13/50) by linarith only [small])
    apply lt_of_not_ge
    intro high
    have bad := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1+x^2 by positivity) (show 49/100-s≤0 by linarith only [high])
    nlinarith only [bad,sine,product]
  have strict : c<1 := by nlinarith only [cn.2.2,sp,cb.2.1,sq_pos_of_pos sp]
  exact ⟨sp,close,narrow,strict⟩

private theorem disk_bound {c s P R : ℝ} (unit : c^2+s^2=1)
    (disk : P^2+R^2≤1) : P*c+R*s≤1 := by
  have identity : (P*c+R*s)^2+(P*s-R*c)^2=P^2+R^2 := by
    linear_combination (P^2+R^2)*unit
  nlinarith only [identity,disk,sq_nonneg (P*s-R*c)]

/-- The displayed cubic's completed square is positive on the full
closed successor half-angle interval. No sampled subinterval is used. -/
theorem longitudinal_margin {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t) :
    0≤1+(c*t+s*d)-c-(c*t+s*d)*d-(c*t+s*d)*t/2+
      (13/50)*(c*d-s*t)*t := by
  have db := normal_bounds dn
  have dp : 0<d := by linarith only [db.1]
  let y := half d t
  have data := quarter_data d t dp.le dn.1 dn.2.2
  have yn : 0≤y := data.1
  have cosine : (1+y^2)*d=1-y^2 := data.2.2.2.1
  have sine : (1+y^2)*t=2*y := data.2.2.2.2
  have order := mul_nonneg (show 0≤1+y^2 by positivity) (sub_nonneg.mpr dn.2.1)
  have sector : y≤5/12 := by
    apply le_of_not_gt
    intro high
    have square := mul_pos (show 0<y-5/12 by linarith only [high])
      (show 0<y+5/12 by linarith only [yn])
    nlinarith only [cosine,sine,order,square,high]
  let P := 1-t+t^2/2+(37/50)*d*t
  let R := 1-d+d*t/2-(37/50)*t^2
  have den : 1+y^2≠0 := by positivity
  have dc : d=(1-y^2)/(1+y^2) := (eq_div_iff den).mpr (by nlinarith only [cosine])
  have tc : t=(2*y)/(1+y^2) := (eq_div_iff den).mpr (by nlinarith only [sine])
  have identity : (1+y^2)^2*(1-P^2-R^2)=
      (2/625)*y*(325-1647*y+3425*y^2-1250*y^3) := by
    dsimp only [P,R]
    rw [dc,tc]
    field_simp [den]
    ring
  have coefficient : 17425/6≤3425-1250*y := by linarith only [sector]
  have product := mul_nonneg (sq_nonneg y) (sub_nonneg.mpr coefficient)
  have square := sq_nonneg (y-4941/17425)
  have cubic : 0<325-1647*y+3425*y^2-1250*y^3 := by
    nlinarith only [product,square]
  have scaled : 0≤(1+y^2)^2*(1-P^2-R^2) := by
    rw [identity]
    exact mul_nonneg (mul_nonneg (by norm_num) yn) cubic.le
  have disk : P^2+R^2≤1 := by
    apply le_of_not_gt
    intro high
    have bad := mul_neg_of_pos_of_neg
      (show 0<(1+y^2)^2 by positivity)
      (show 1-P^2-R^2<0 by linarith only [high])
    linarith only [scaled,bad]
  have bound := disk_bound cn.2.2 disk
  have exactMargin :
      1+(c*t+s*d)-c-(c*t+s*d)*d-(c*t+s*d)*t/2+(13/50)*(c*d-s*t)*t=
        1-P*c-R*s := by
    dsimp only [P,R]
    linear_combination -s*dn.2.2
  rw [exactMargin]
  linarith only [bound]

/-- The actual neighboring-marker cap replaces every unsupported
backward-inner cap. Only the proved coarse source-angle bounds are used. -/
theorem transverse_margin {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (close : 87/100<c) (small : s<49/100) :
    0<1+(c*d-s*t)+(c*t+s*d)-d-t/2-(c*t+s*d)*c-
      (7/20)*(c*d-s*t)*(c-s) := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  have dp : 0<d := by linarith only [db.1]
  let P := 1-c-s+(13/20)*c*s+(7/20)*c^2
  let R := 3/2-c+s-(7/20)*c*s-(13/20)*s^2
  have pc : P<2/5 := by
    have first := mul_nonpos_of_nonneg_of_nonpos cn.1
      (show (13/20)*c-1≤0 by linarith only [cb.2.1])
    have second := mul_neg_of_pos_of_neg
      (show 0<c-87/100 by linarith only [close])
      (show (7/20)*(c+87/100)-1<0 by linarith only [cb.2.1])
    dsimp only [P]
    nlinarith only [first,second]
  have rc : R<41/50 := by
    have product := mul_nonneg cn.1 (show 0≤c-87/100 by linarith only [close])
    have square := sq_nonneg (s-1391/2600)
    dsimp only [R]
    nlinarith only [product,square,close]
  have weighted := mul_pos dp (sub_pos.mpr pc)
  have other := mul_nonneg dn.1 (sub_nonneg.mpr rc.le)
  have circle : ((2/5)*d+(41/50)*t)^2+((2/5)*t-(41/50)*d)^2=2081/2500 := by
    linear_combination (2081/2500)*dn.2.2
  have norm : (2/5)*d+(41/50)*t<1 := by
    nlinarith only [circle,sq_nonneg ((2/5)*t-(41/50)*d)]
  have exactMargin : 1+(c*d-s*t)+(c*t+s*d)-d-t/2-(c*t+s*d)*c-
      (7/20)*(c*d-s*t)*(c-s)=1-P*d-R*t := by
    dsimp only [P,R]
    linear_combination -t*cn.2.2
  rw [exactMargin]
  nlinarith only [weighted,other,norm]

end N12Compact.C1092MPPMNegativeForward
