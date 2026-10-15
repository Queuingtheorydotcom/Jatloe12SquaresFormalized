import Compact.Completion.C981.HalfAngle
import Compact.Geometry.C977CornerCubic

/-! The rational scalar ending in C981-COMMON-CYCLE Theorem 3.
No derivative, angle mesh or numerical oracle is used. -/
namespace N12Compact.C981CompletionAngularScalars

open C977CornerCubic
set_option Elab.async false

/-- A negative central square's final correlated support cut is incompatible
with a positive neighbor whose half-angle is at least 7/18. -/
theorem impossible (d r b t : ℝ) (cn : Normal d r) (bn : Normal b t)
    (angle : 7/18 ≤ C981CompletionHalfAngle.half b t)
    (cut : 1 < b*(1-r*(1-(7/20)*(d+r)))+t*(1-d*(1-(7/20)*(d+r)))) : False := by
  classical
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have dp : 0 < d := by linarith only [cb.1]
  have bp : 0 < b := by linarith only [bb.1]
  let H := d+r
  let q := 1-(7/20)*H
  let F := 1-r*q
  let G := 1-d*q
  change 1 < b*F+t*G at cut
  have Hlow : 1 ≤ H := cb.2.2.2.2.1
  have Hhigh : H ≤ 10/7 := cb.2.2.2.2.2
  have normIdentity : (b*F+t*G)^2+(b*G-t*F)^2=(b^2+t^2)*(F^2+G^2) := by ring
  rw [bn.2.2,one_mul] at normIdentity
  have positiveSquare := mul_pos (sub_pos.mpr cut)
    (show 0 < b*F+t*G+1 by linarith only [cut])
  have normLarge : 1 < F^2+G^2 := by
    nlinarith only [normIdentity,positiveSquare,sq_nonneg (b*G-t*F)]
  have polynomial : F^2+G^2-1=2-(27/10)*H+(329/400)*H^2 := by
    calc
      _ = 1-2*(d+r)*q+(d^2+r^2)*q^2 := by dsimp [F,G]; ring
      _ = _ := by rw [cn.2.2]; dsimp [H,q]; ring
  have Hsmall : H < 113/100 := by
    apply lt_of_not_ge
    intro large
    have coefficient : -(27/10)+(329/400)*(H+113/100) ≤ 0 := by
      linarith only [Hhigh]
    have product := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ H-113/100 by linarith only [large]) coefficient
    have identity :
        2-(27/10)*H+(329/400)*H^2 = -(2999/4000000)+
          (H-113/100)*(-(27/10)+(329/400)*(H+113/100)) := by ring
    have negative : F^2+G^2-1 < 0 := by
      rw [polynomial, identity]
      calc
        _ ≤ -(2999/4000000)+0 := add_le_add_left product _
        _ < 0 := by norm_num
    exact (sub_pos.mpr normLarge).not_le negative.le
  have rSmall : r < 7/50 := by
    apply lt_of_not_ge
    intro large
    have rHalf : r < 113/200 := by dsimp [H] at Hsmall; linarith only [Hsmall,cn.2.1]
    have comparison := mul_nonneg
      (show 0 ≤ 113/100-r-d by dsimp [H] at Hsmall; linarith only [Hsmall])
      (show 0 ≤ 113/100-r+d by linarith only [rHalf,dp])
    have interval := mul_nonneg (show 0 ≤ r-7/50 by linarith only [large])
      (show 0 ≤ 99/100-r by linarith only [rHalf])
    nlinarith only [comparison,interval,cn.2.2]
  have dLarge : 99/100 < d := by
    apply lt_of_not_ge
    intro small
    have comparison := mul_nonneg (show 0 ≤ 99/100-d by linarith only [small])
      (show 0 ≤ 99/100+d by linarith only [dp])
    have sine := mul_pos (show 0 < 7/50-r by linarith only [rSmall])
      (show 0 < 7/50+r by linarith only [cn.1])
    nlinarith only [comparison,sine,cn.2.2]
  have qLower : 1209/2000 < q := by dsimp [q]; linarith only [Hsmall]
  have qUpper : q ≤ 1 := by
    change 1-(7/20)*H ≤ 1
    exact sub_le_self _ (mul_nonneg (by norm_num) (zero_le_one.trans Hlow))
  have FUpper : F ≤ 1-(1209/2000)*r := by
    have product := mul_nonneg cn.1 (show 0 ≤ q-1209/2000 by linarith only [qLower])
    dsimp [F]; nlinarith only [product]
  have FLower : 43/50 < F := by
    have rq : r*q ≤ r := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left qUpper cn.1
    change 43/50 < 1-r*q
    calc
      43/50 = 1-7/50 := by norm_num
      _ < 1-r := sub_lt_sub_left rSmall 1
      _ ≤ 1-r*q := sub_le_sub_left rq 1
  have defect : 1-d ≤ (3/5)*r^2 := by
    have product := mul_nonneg (sub_nonneg.mpr cb.2.1)
      (show 0 ≤ 3*d-2 by linarith only [dLarge])
    nlinarith only [product,cn.2.2]
  have GIdentity : G=7/20+(1-d)-(7/20)*r^2+(7/20)*d*r := by
    dsimp [G,q,H]
    linear_combination (7/20)*cn.2.2
  have GUpper : G ≤ 7/20+(77/200)*r := by
    have first := mul_nonneg cn.1 (sub_nonneg.mpr cb.2.1)
    have second := mul_nonneg cn.1 (show 0 ≤ 7/50-r by linarith only [rSmall])
    nlinarith only [GIdentity,defect,first,second]
  have GCoarse : G ≤ 4039/10000 := by linarith only [GUpper,rSmall]
  have angleLinear : 7*(1+b) ≤ 18*t := by
    have cp : 0 < 1+b := by linarith only [bp]
    have inequality := (le_div_iff₀ cp).mp angle
    linarith only [inequality]
  have tLower : 252/373 ≤ t := by
    apply le_of_not_gt
    intro small
    have bSmall : b < 275/373 := by linarith only [small,angleLinear]
    have first := mul_pos (show 0 < 275/373-b by linarith only [bSmall])
      (show 0 < 275/373+b by linarith only [bp])
    have last := mul_pos (show 0 < 252/373-t by linarith only [small])
      (show 0 < 252/373+t by linarith only [bn.1])
    nlinarith only [first,last,bn.2.2]
  have support : 275*b+252*t ≤ 373 := by
    have identity : (275*b+252*t)^2+(252*b-275*t)^2=373^2*(b^2+t^2) := by ring
    rw [bn.2.2] at identity
    nlinarith only [identity,sq_nonneg (252*b-275*t),sq_nonneg (275*b+252*t-373)]
  have order : 0 ≤ 252*F-275*G := by
    have lower : (252:ℝ)*(43/50)-275*(4039/10000) ≤ 252*F-275*G :=
      sub_le_sub (mul_le_mul_of_nonneg_left FLower.le (by norm_num))
        (mul_le_mul_of_nonneg_left GCoarse (by norm_num))
    exact le_trans (by norm_num) lower
  have first := mul_nonneg
    ((show (0:ℝ) < 43/50 by norm_num).trans FLower).le
    (show 0 ≤ 373-275*b-252*t by linarith only [support])
  have second := mul_nonneg (show 0 ≤ t-252/373 by linarith only [tLower]) order
  have endpoint : b*F+t*G ≤ (275*F+252*G)/373 := by
    have sum := add_nonneg first second
    have identity : F*(373-275*b-252*t)+(t-252/373)*(252*F-275*G) =
        275*((275*F+252*G)/373-(b*F+t*G)) := by ring
    rw [identity] at sum
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right sum (by norm_num))
  have upper : (275*F+252*G)/373 ≤
      (275*(1-(1209/2000)*r)+252*(7/20+(77/200)*r))/373 :=
    div_le_div_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left FUpper (by norm_num))
        (mul_le_mul_of_nonneg_left GUpper (by norm_num))) (by norm_num)
  have short : (275*(1-(1209/2000)*r)+252*(7/20+(77/200)*r))/373 < 1 := by
    linarith only [cn.1]
  exact (not_lt_of_ge short.le) (lt_of_lt_of_le cut (le_trans endpoint upper))

#print axioms impossible
end N12Compact.C981CompletionAngularScalars
