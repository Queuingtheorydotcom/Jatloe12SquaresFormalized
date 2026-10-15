import Compact.Completion.C1092.MPPMMissingNegativeCrosspointG11

/-! Fixed scalar models for the missing-negative G01 support. The small
arc uses one exact quadratic-circle chord. On the large arc a difference
from the diagonal factors through h+r and r-h. No angular derivatives,
sampled angles, or open endpoint restrictions are used. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointSupport
open C977CornerCubic C1092ShallowPositiveScalars
open C1092MPPMCrosspointSupport
set_option Elab.async false
noncomputable section

private theorem low_remainder (b z : ℝ) (bl : 3/5≤b) (bu : b≤71/100)
    (zn : 0≤z) (zu : z≤1/3) :
    0≤QuadraticArc.remainder (4/5) b (b-1/100) 0 z (1/3) := by
  let X := z^2+(1/3:ℝ)^2+z^2*(1/3:ℝ)^2
  have square := mul_nonneg (show 0≤1/3-z by linarith only [zu])
    (show 0≤1/3+z by linarith only [zn])
  have Xn : 0≤X := by dsimp [X]; positivity
  have Xu : X≤19/81 := by dsimp [X]; nlinarith only [square]
  have weight := mul_le_mul_of_nonneg_right
    (show 79/100+b≤3/2 by linarith only [bu]) Xn
  have positive := mul_nonneg zn (show 0≤2*b-8/15 by linarith only [bl])
  have identity : QuadraticArc.remainder (4/5) b (b-1/100) 0 z (1/3)=
      81/100-b-(79/100+b)*X+(2*b-8/15)*z+(2/3)*b := by
    dsimp [QuadraticArc.remainder,QuadraticArc.X,QuadraticArc.Y,QuadraticArc.Z,
      QuadraticArc.sum3,QuadraticArc.pair3,QuadraticArc.triple3,X]
    ring
  nlinarith only [identity,weight,positive,Xu,bl,bu]

theorem G01_low_model (b h r : ℝ) (bl : 3/5≤b) (bu : b≤71/100)
    (q : Quarter h r) (hh : 4/5≤h) (rr : r≤3/5) :
    1/100≤(4/5)*h^2+b*h*r+b-(3/5+(112/125)*b)*h-(61/50)*b*r := by
  have bn : Normal h r := ⟨q.sine,by linarith only [hh,rr],q.unit⟩
  have hd := normal_half bn
  have endpoint : Normal (4/5:ℝ) (3/5) := by norm_num [Normal]
  have order := half_order bn endpoint rr
  have zu : half h r≤1/3 := by norm_num [half] at order; exact order
  have rem := low_remainder b (half h r) bl bu hd.1 zu
  have first : 0≤QuadraticArc.value (4/5) b (b-1/100)
      (-(3/5+(112/125)*b)) (-(61/50)*b) 0 := by
    norm_num [QuadraticArc.value,cosH,sinH]
    linarith only [bl]
  have last : 0≤QuadraticArc.value (4/5) b (b-1/100)
      (-(3/5+(112/125)*b)) (-(61/50)*b) (1/3) := by
    norm_num [QuadraticArc.value,cosH,sinH]
    linarith only [bl]
  have result := QuadraticArc.nonnegative (4/5) b (b-1/100)
    (-(3/5+(112/125)*b)) (-(61/50)*b) 0 (half h r) (1/3)
    (by norm_num) hd.1 zu rem first last
  dsimp [QuadraticArc.value] at result
  rw [hd.2.2.2.1,hd.2.2.2.2] at result
  linarith only [result]

theorem G01_middle_model (h r : ℝ) (bn : Normal h r) (steep : 3/5≤r) :
    1/100≤2*h+r-2-(112/125)*h*r+(39/50)*r^2 := by
  have result := middle_scalar_lower h r bn steep
  have positive := mul_nonneg (show 0≤h by linarith only [(normal_bounds bn).1])
    (show 0≤(9/200)*h-(41/1000)*r by linarith only [bn.2.1,bn.1])
  nlinarith only [result,positive,bn.2.2]

theorem G01_high_model (h r : ℝ) (q : Quarter h r) (order : h≤r) :
    1/100≤(4/5)*h^2+(151/100)*h*r+(71/100)*r^2-
      (10211/6250)*h-(1207/2500)*r := by
  let w := Real.sqrt 2/2
  let H := h+r
  let D := r-h
  have wn : 0≤w := by dsimp [w]; positivity
  have wu : 2*w^2=1 := by
    dsimp [w]
    nlinarith only [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  have wh : w≤177/250 := by nlinarith only [wu,wn,sq_nonneg (w-177/250)]
  have Hn : 0≤H := add_nonneg q.cosine q.sine
  have Dn : 0≤D := sub_nonneg.mpr order
  have rh : r≤1 := by nlinarith only [q.unit,sq_nonneg h,sq_nonneg (r-1)]
  have Dh : D≤1 := by dsimp [D]; linarith only [rh,q.cosine]
  have unit : H^2+D^2=2 := by dsimp [H,D]; nlinarith only [q.unit]
  have Hh : H≤2*w := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<H-2*w by linarith only [bad])
      (show 0<H+2*w by linarith only [bad,wn])
    nlinarith only [product,unit,wu,sq_nonneg D]
  have gap : 0≤2*w-H := sub_nonneg.mpr Hh
  have product := mul_nonneg gap
    (show 0≤20/7-(2*w+H) by linarith only [Hh,wh])
  have chord : (7/20)*D^2≤2*w-H := by nlinarith only [product,unit,wu]
  have bracket : 0≤14387/25000-(9/200)*H-(192301/500000)*D := by
    linarith only [Hh,wh,Dh]
  have positive := mul_nonneg Dn bracket
  have identity : (4/5)*h^2+(151/100)*h*r+(71/100)*r^2-
      (10211/6250)*h-(1207/2500)*r-
      (151/100-(26457/12500)*w)=
      (26457/25000)*(2*w-H)-(151/200)*D^2+
        D*(14387/25000-(9/200)*H) := by
    dsimp [H,D]
    linear_combination (151/100)*q.unit
  nlinarith only [identity,chord,positive,wh]

end
end N12Compact.C1092MPPMMissingNegativeCrosspointSupport
