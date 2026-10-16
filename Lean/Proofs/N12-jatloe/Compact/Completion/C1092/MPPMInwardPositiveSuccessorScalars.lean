import Compact.Completion.C1092.MPPMInwardPositiveProfile
import Compact.Completion.CommonCases.UnitCircleChord
import Compact.Geometry.C977CornerSectorBounds

/-! Whole-arc margins for POSITIVE-MISSING-INWARD-SUCCESSOR.
The two downward comparisons use rational canonical sum bounds. In
particular the ordered relative-angle lower bound is a circle chord,
not an angular derivative or orientation sample. -/
namespace N12Compact.C1092MPPMInwardPositive.SuccessorScalars
open C977CornerCubic
set_option Elab.async false
noncomputable section

def k (c s d t : ℝ) : ℝ := c*d+s*t
def delta (c s d t : ℝ) : ℝ := c*t-s*d
def A (c s : ℝ) : ℝ := 27/20-c+s-(3/4)*s^2-(13/20)*c*s
def B (c s : ℝ) : ℝ := 2-c-s-(13/20)*s^2+(3/4)*c*s

theorem relative {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    0<k c s d t ∧ k c s d t≤1 := by
  have cp : 0<c := by linarith only [(normal_bounds cn).1]
  have dp : 0<d := by linarith only [(normal_bounds en).1]
  have first := mul_pos cp dp
  have last := mul_nonneg cn.1 en.1
  constructor
  · dsimp [k]; linarith only [first,last]
  · dsimp [k]
    nlinarith only [cn.2.2,en.2.2,sq_nonneg (c-d),sq_nonneg (s-t)]

theorem source_margin {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (large : 3/5<t) :
    0<1-c-(2/5)*s+k c s d t*(1-d+(2/5)*t)-(7/20)*delta c s d t*(d+t) := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  let P := 2-d-(13/20)*t^2-(1/20)*d*t
  let Q := t-(13/20)*d*t-(1/20)*d^2
  have order := mul_nonneg (sub_nonneg.mpr en.2.1)
    (show 0≤d+t by linarith only [dp,en.1])
  have t2 : t^2≤1/2 := by nlinarith only [order,en.2.2]
  have dt : d*t≤1/2 := by nlinarith only [en.2.2,sq_nonneg (d-t)]
  have pn : 0<P := by dsimp [P]; nlinarith only [eb.2.1,t2,dt]
  have chord := mul_nonneg (show 0≤1-d by linarith only [eb.2.1])
    (show 0≤(13/20)*(1+d)-1 by linarith only [eb.1])
  have product := mul_pos dp (show 0<t by linarith only [large])
  have pu : P<1 := by dsimp [P]; nlinarith only [chord,product,en.2.2]
  have low := mul_nonneg en.1 (show 0≤1-d by linarith only [eb.2.1])
  have qn : 0≤Q := by dsimp [Q]; nlinarith only [low,large,eb.2.1,en.2.2,sq_nonneg t]
  have first := mul_nonneg pn.le (show 0≤1-c by linarith only [cb.2.1])
  have last := mul_nonneg cn.1 qn
  have identity : 1-c-(2/5)*s+k c s d t*(1-d+(2/5)*t)-
      (7/20)*delta c s d t*(d+t)=1-P*c+Q*s := by
    dsimp [k,delta,P,Q]
    linear_combination (-c+(2/5)*s)*en.2.2
  nlinarith only [identity,first,last,pu]

theorem downward_margin {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    0<1-(7/20)*(c+s)-(7/20)*k c s d t*(d+t) := by
  have cs := C1092MPPMActualNonordinary.normal_sum c s cn
  have es := C1092MPPMActualNonordinary.normal_sum d t en
  have rel := relative cn en
  have product := mul_nonneg (show 0≤1-k c s d t by linarith only [rel.2])
    (show 0≤d+t by linarith only [es.1])
  nlinarith only [cs.2.1,es.2.1,product]

theorem coefficient_bounds {c s : ℝ} (cn : Normal c s) :
    A c s≤13/20 ∧ A c s+B c s≤7/5 := by
  have cb := normal_bounds cn
  have sum := C1092MPPMActualNonordinary.normal_sum c s cn
  have first := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤1-(7/10)*(c+s) by linarith only [sum.2.1])
  have last := mul_nonneg cn.1 (sub_nonneg.mpr cn.2.1)
  have deficit := mul_nonneg (show 0≤1-c by linarith only [cb.2.1])
    (show 0≤(3/5)*(1+c)-1 by linarith only [cb.1])
  have cross : c*s≤1/2 := by nlinarith only [cn.2.2,sq_nonneg (c-s)]
  dsimp [A,B]
  constructor <;> nlinarith only [first,last,deficit,cross,cn.2.2,sq_nonneg s]

theorem target_after {c s d t : ℝ} (cn : Normal c s) (en : Normal d t) :
    0<1-d-t+k c s d t*(1-(7/20)*(c+s))+
      delta c s d t*(1-c-(2/5)*s) := by
  have coefficients := coefficient_bounds cn
  have es := C1092MPPMActualNonordinary.normal_sum d t en
  let P := A c s
  let Q := B c s
  have identity : 1-d-t+k c s d t*(1-(7/20)*(c+s))+
      delta c s d t*(1-c-(2/5)*s)=1-P*d-Q*t := by
    dsimp [k,delta,P,Q,A,B]
    linear_combination (-(7/20)*d-t)*cn.2.2
  by_cases order : P≤Q
  · have first := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr en.2.1)
      (show P-Q≤0 by linarith only [order])
    have last := mul_nonneg (show 0≤7/5-P-Q by linarith only [coefficients.2])
      (show 0≤d+t by linarith only [es.1])
    nlinarith only [identity,first,last,es.2.1]
  · have first := mul_nonneg en.1 (show 0≤P-Q by linarith only [order])
    have last := mul_nonneg (show 0≤13/20-P by exact sub_nonneg.mpr coefficients.1)
      (show 0≤d+t by linarith only [es.1])
    nlinarith only [identity,first,last,es.2.1]

private theorem ordered_relative_lower {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (order : delta c s d t≤0) : (7/10)*(d+t)≤k c s d t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  let v := Real.sqrt 2/2
  have vp : 0≤v := by dsimp [v]; positivity
  have vu : v^2+v^2=1 := by
    dsimp [v]
    nlinarith only [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  have vl : 7/10≤v := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<7/10-v by linarith only [bad])
      (show 0<7/10+v by linarith only [vp])
    nlinarith only [product,vu]
  have angles : t≤s := C977CornerSectorBounds.sine_order cn en order
  have sh : s≤v := by
    have product := mul_nonneg (sub_nonneg.mpr cn.2.1)
      (show 0≤c+s by linarith only [cb.1,cn.1])
    apply le_of_not_gt
    intro high
    have square := mul_pos (sub_pos.mpr high)
      (show 0<s+v by linarith only [high,vp])
    nlinarith only [product,square,vu,cn.2.2]
  have sum := C1092MPPMActualNonordinary.normal_sum d t en
  have last := mul_nonneg (sub_nonneg.mpr vl) (show 0≤d+t by linarith only [sum.1])
  have chord := CommonCases.UnitCircleChord.linear_nonnegative
    (c:=d) (s:=t) (d:=v) (t:=v) (h:=c) (r:=s)
    (b:=-(7/10)*(d+t)) (A:=d) (B:=t)
    (by linarith only [eb.1]) vp (by linarith only [cb.1]) en.2.2 vu cn.2.2
    angles sh (by linarith only [eb.1])
    (by nlinarith only [sum.2.1,en.2.2]) (by nlinarith only [last])
  dsimp [k]
  linarith only [chord]

theorem target_before {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (order : delta c s d t≤0) :
    0<1-d-t+k c s d t*(1-(7/20)*(c+s)) := by
  have cs := C1092MPPMActualNonordinary.normal_sum c s cn
  have es := C1092MPPMActualNonordinary.normal_sum d t en
  have rel := relative cn en
  have lower := ordered_relative_lower cn en order
  have first := mul_nonneg rel.1.le (show 0≤1-(7/20)*(c+s)-1/2 by linarith only [cs.2.1])
  nlinarith only [first,lower,es.2.1]

end
#print axioms source_margin
#print axioms target_after
#print axioms target_before
end N12Compact.C1092MPPMInwardPositive.SuccessorScalars
