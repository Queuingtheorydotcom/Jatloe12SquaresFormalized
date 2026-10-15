import Compact.Completion.C1092.WholeSupports
import Compact.Geometry.C977CornerCubic

/-! Uniform scalar margins for the actual mixed-wall/corner obstruction.
All bounds include canonical axis endpoints and relative-angle equality. -/
namespace N12Compact.C1092MixedCornerScalars
open C977CornerCubic
set_option Elab.async false

theorem elementary {c s : ℝ} (cn : Normal c s) :
    7/10<c ∧ s^2≤1/2 ∧ c*s≤1/2 := by
  have cb := normal_bounds cn
  have order := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (add_nonneg (show 0≤c by linarith only [cb.1]) cn.1)
  refine ⟨?_,?_,?_⟩
  · nlinarith only [order,cn.2.2,cb.1]
  · nlinarith only [order,cn.2.2]
  · nlinarith only [sq_nonneg (c-s),cn.2.2]

theorem common {d r : ℝ} (dn : Normal d r) (rp : 0<r) :
    1/10≤d-9/10+(4/5)*r^2 ∧
      0<r*(1-(4/5)*d) ∧ 0<d+r-(9/10)*d*r ∧
      1/50≤d-9/10+(4/5)*r^2-(2/5)*(r*(1-(4/5)*d)) := by
  have db := normal_bounds dn
  have dp : 0<d := by linarith only [db.1]
  have defect := mul_nonneg (sub_nonneg.mpr db.2.1)
    (show 0≤(4/5)*d-1/5 by linarith only [db.1])
  have first : 1/10≤d-9/10+(4/5)*r^2 := by
    nlinarith only [defect,dn.2.2]
  have second : 0<r*(1-(4/5)*d) :=
    mul_pos rp (by linarith only [db.2.1])
  have third : 0<d+r-(9/10)*d*r := by
    have last := mul_nonneg rp.le (show 0≤1-(9/10)*d by linarith only [db.2.1])
    nlinarith only [dp,last]
  have factor : 0≤(4/5)*d-1/5-(8/25)*r := by
    linarith only [dn.2.1,db.1]
  have product := mul_nonneg (sub_nonneg.mpr db.2.1) factor
  have last : 1/50≤d-9/10+(4/5)*r^2-(2/5)*(r*(1-(4/5)*d)) := by
    nlinarith only [product,dn.2.2,db.2.2.2.1]
  exact ⟨first,second,third,last⟩

theorem nonnegative_pair {d r c s : ℝ} (dn : Normal d r) (cn : Normal c s)
    (rp : 0<r) :
    d*((1/5)*c^2+(1/2)*c*s-c)+
      r*(1/10+(1/2)*s^2-s+(1/5)*c*s)<0 := by
  have cb := normal_bounds cn
  have bounds := elementary cn
  have square : c^2≤1 := by nlinarith only [cn.2.2,sq_nonneg s]
  have f : (1/5)*c^2+(1/2)*c*s-c≤-1/4 := by
    nlinarith only [square,bounds.2.2,cb.1]
  have sum : ((1/5)*c^2+(1/2)*c*s-c)+
      (1/10+(1/2)*s^2-s+(1/5)*c*s)≤-1/5 := by
    nlinarith only [cn.2.2,bounds.2.1,bounds.2.2,cb.2.2.2.2.1]
  have a := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr dn.2.1)
    (f.trans (by norm_num))
  have b := mul_neg_of_pos_of_neg rp (sum.trans_lt (by norm_num))
  calc
    _ = (d-r)*((1/5)*c^2+(1/2)*c*s-c)+
        r*(((1/5)*c^2+(1/2)*c*s-c)+(1/10+(1/2)*s^2-s+(1/5)*c*s)) := by ring
    _ < 0 := add_neg_of_nonpos_of_neg a b

theorem upper_u_pair {d r c s : ℝ} (dn : Normal d r) (cn : Normal c s)
    (rp : 0<r) (ratio : s<(2/5)*c) :
    9/10<c ∧ s<2/5 ∧
      d*((1/5)*c^2-(1/2)*c*s-c)+
        r*(1/10+(1/2)*s^2+s-(1/5)*c*s)<0 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have product := mul_pos (sub_pos.mpr ratio)
    (show 0<(2/5)*c+s by linarith only [cp,cn.1])
  have cosine : 9/10<c := by nlinarith only [product,cn.2.2,cp]
  have sine : s<2/5 := ratio.trans_le (by linarith only [cb.2.1])
  have square : c^2≤1 := by nlinarith only [cn.2.2,sq_nonneg s]
  have sSquare : s^2<4/25 := by
    nlinarith only [mul_pos (sub_pos.mpr sine)
      (show 0<(2/5)+s by linarith only [cn.1])]
  have cs := mul_nonneg cp.le cn.1
  have f : (1/5)*c^2-(1/2)*c*s-c < -7/10 := by
    nlinarith only [square,cs,cosine]
  have g : 1/10+(1/2)*s^2+s-(1/5)*c*s < 29/50 := by
    nlinarith only [sSquare,sine,cs]
  have a := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr dn.2.1)
    (f.le.trans (by norm_num))
  have b := mul_neg_of_pos_of_neg rp
    (show ((1/5)*c^2-(1/2)*c*s-c)+(1/10+(1/2)*s^2+s-(1/5)*c*s)<0 by
      linarith only [f,g])
  refine ⟨cosine,sine,?_⟩
  calc
    _ = (d-r)*((1/5)*c^2-(1/2)*c*s-c)+
        r*(((1/5)*c^2-(1/2)*c*s-c)+(1/10+(1/2)*s^2+s-(1/5)*c*s)) := by ring
    _ < 0 := add_neg_of_nonpos_of_neg a b

theorem upper_v_pair {d r c s : ℝ} (dn : Normal d r) (cn : Normal c s)
    (rp : 0<r) : d*((1/5)*s^2-s)+r*(3/5-c+(1/5)*c*s)<0 := by
  have db := normal_bounds dn
  have cb := normal_bounds cn
  have bounds := elementary cn
  have first : (1/5)*s^2-s≤0 := by
    have product := mul_nonpos_of_nonneg_of_nonpos cn.1
      (show (1/5)*s-1≤0 by linarith only [cb.2.2.2.1])
    nlinarith only [product]
  have last : 3/5-c+(1/5)*c*s<0 := by
    linarith only [bounds.1,bounds.2.2]
  exact add_neg_of_nonpos_of_neg
    (mul_nonpos_of_nonneg_of_nonpos (by linarith only [db.1]) first)
    (mul_neg_of_pos_of_neg rp last)

#print axioms common
#print axioms nonnegative_pair
#print axioms upper_u_pair
#print axioms upper_v_pair
end N12Compact.C1092MixedCornerScalars
