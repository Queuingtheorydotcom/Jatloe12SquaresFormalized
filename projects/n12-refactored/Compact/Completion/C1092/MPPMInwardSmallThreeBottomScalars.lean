import Compact.Completion.C1092.MPPMInwardSmallThreeData

/-! The actual bottom-square tilt bound in SMALL-INWARD-THREE-SQUARE-
ENDING §3. The negative-sign step uses one relative-circle identity:
it proves -sin(beta)<sin(p)/5 directly, without tangent convexity. -/
namespace N12Compact.C1092MPPMInwardSmallThree
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem positive_source_margin {c s h k : ℝ} (cn : Normal c s) (bn : Normal h k)
    (small : half c s≤53/500) : 0<h*(c^2/2+s)+k*(c-c*s/2-543/500) := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have bounds := small_bounds cn small
  let P := c^2/2+s
  let R := c-c*s/2-543/500
  have pp : 0<P := by dsimp [P]; nlinarith only [cb.1,cn.1,sq_nonneg (c-7/10)]
  have first := mul_pos (show 0<c by linarith only [cb.1])
    (show 0<c-s-19/25 by linarith only [bounds.1,bounds.2])
  have sum : 0<P+R := by dsimp [P,R]; nlinarith only [first,bounds.1,cn.1]
  have remainder := mul_nonneg (sub_nonneg.mpr bn.2.1) pp.le
  by_cases zero : k=0
  · have positive := mul_pos (show 0<h by linarith only [bb.1]) pp
    dsimp [P,R] at positive ⊢
    simpa only [zero,zero_mul,add_zero] using positive
  · have positive := mul_pos (lt_of_le_of_ne bn.1 (Ne.symm zero)) sum
    dsimp [P,R] at remainder positive
    nlinarith only [remainder,positive]

theorem positive_tilt {c s h k : ℝ} (cn : Normal c s) (bn : Normal h k)
    (small : half c s≤53/500) (j : J0 c s<0) (jl : -J0 c s≤s^2/10)
    (wall : h*J0 c s+(1-h)^2/2+k*(h/2+c-s-c^2+(2/5)*c*s)<0) : k<21/1000 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have bounds := small_bounds cn small
  have cosine := mul_nonneg (show 0≤c by linarith only [cb.1])
    (show 0≤1-c by linarith only [cb.2.1])
  have first := mul_nonneg cn.1 (show 0≤(153/250)-(1-(2/5)*c) by linarith only [bounds.1])
  have coefficient : -(13/100)<c-s-c^2+(2/5)*c*s := by
    nlinarith only [cosine,first,bounds.2]
  have weight := mul_nonneg bn.1
    (show 0≤h/2+c-s-c^2+(2/5)*c*s-11/50 by linarith only [coefficient,bb.1])
  have negative := mul_nonneg (show 0≤1-h by linarith only [bb.2.1]) (neg_nonneg.mpr j.le)
  have square := mul_pos (show 0<21/100-s by linarith only [bounds.2])
    (show 0<21/100+s by linarith only [cn.1])
  nlinarith only [wall,weight,negative,jl,sq_nonneg (1-h),square]

theorem negative_tilt {c s h l : ℝ} (cn : Normal c s) (bn : Normal h l)
    (positive : 0<s) (gamma : 0<s*h-c*l)
    (separation : c*h+s*l+Q c s*(s*h-c*l)<1) : l<s/5 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0<c := by linarith only [cb.1]
  let lam := c*h+s*l
  let gam := s*h-c*l
  have lp : 0<lam := by
    have first := mul_pos cp (show 0<h by linarith only [bb.1])
    have last := mul_nonneg cn.1 bn.1
    dsimp [lam]; nlinarith only [first,last]
  have unit : lam^2+gam^2=1 := by
    dsimp [lam,gam]
    linear_combination (h^2+l^2)*cn.2.2+bn.2.2
  have first := mul_pos (show 0<1-lam-Q c s*gam by linarith only [separation])
    (show 0<1+lam by linarith only [lp])
  have scaled : 0<gam*(gam-Q c s*(1+lam)) := by nlinarith only [first,unit]
  have gap := pos_of_mul_pos_right scaled gamma.le
  have floor := mul_nonneg (show 0≤1-c by linarith only [cb.2.1])
    (show 0≤c-(2/5)*s by linarith only [cn.2.1,cn.1])
  have Qfloor : (2/5)*s≤c*Q c s := by dsimp [Q]; nlinarith only [floor]
  have weighted := mul_nonneg (sub_nonneg.mpr Qfloor) (show 0≤1+lam by linarith only [lp])
  have strict := mul_pos cp gap
  have support : 0<c*gam-(2/5)*s*(1+lam) := by nlinarith only [strict,weighted]
  have cap := mul_nonneg (show 0≤1-c by linarith only [cb.2.1])
    (show 0≤1-(1/5)*(1+c) by linarith only [cb.2.1])
  have side := mul_nonneg cp.le (show 0≤1-h by linarith only [bb.2.1])
  have reserve := mul_nonneg positive.le
    (show 0≤1-c*h-s^2/5 by nlinarith only [cap,side,cn.2.2])
  have identity : (c^2+(2/5)*s^2)*(s/5-l)=
      c*gam-(2/5)*s*(1+lam)+(3/5)*s*(1-c*h-s^2/5) := by
    dsimp [gam,lam]
    linear_combination (s/5)*cn.2.2
  have result : 0<(c^2+(2/5)*s^2)*(s/5-l) := by
    rw [identity]; nlinarith only [support,reserve]
  have bound := pos_of_mul_pos_right result (by positivity : 0≤c^2+(2/5)*s^2)
  linarith only [bound]

end
end N12Compact.C1092MPPMInwardSmallThree
