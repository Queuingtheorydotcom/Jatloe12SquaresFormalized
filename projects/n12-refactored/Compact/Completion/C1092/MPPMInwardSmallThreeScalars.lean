import Compact.Completion.C1092.MPPMInwardFinalBottomAngle
import Compact.Completion.C1092.MPPMNegativeCrosspointG01Quartic
import Compact.Completion.CommonCases.UnitCircleChord

/-! SMALL-INWARD-THREE-SQUARE-ENDING §2. Finite circle differences
and rational endpoint polynomials give the strict successor angle cap.
This file performs no angular sampling and uses no side upper bound. -/
namespace N12Compact.C1092MPPMInwardSmallThree
open C977CornerCubic C1092WallProfileScalars C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

def Q (c s : ℝ) := 1-c+(2/5)*s
def J0 (c s : ℝ) := c+s-1-c*s+(2/5)*s^2
def kappa (c s d t : ℝ) := c*d+s*t
def delta (c s d t : ℝ) := c*t-s*d
def FC (c s d t : ℝ) := Q c s+kappa c s d t*(1-d-t)+delta c s d t*(1-t+(2/5)*d)
def FE (c s d t : ℝ) := 1-d-t+kappa c s d t*Q c s+delta c s d t

theorem small_bounds {c s : ℝ} (cn : Normal c s) (small : half c s≤53/500) :
    97/100<c ∧ s<21/100 := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let x := half c s
  have square := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤53/500+x by linarith only [data.1])
  have first : 0<(1+x^2)*(c-97/100) := by
    nlinarith only [square,data.2.2.2.1]
  have monotone := mul_nonneg (show 0≤53/500-x by exact sub_nonneg.mpr small)
    (show 0≤2-(21/100)*(x+53/500) by linarith only [small])
  have last : 0<(1+x^2)*(21/100-s) := by
    nlinarith only [monotone,data.2.2.2.2]
  constructor
  · have bound := pos_of_mul_pos_right first (show 0≤1+x^2 by positivity)
    linarith only [bound]
  · have bound := pos_of_mul_pos_right last (show 0≤1+x^2 by positivity)
    linarith only [bound]

theorem j_bounds {c s : ℝ} (cn : Normal c s) (positive : 0<s)
    (arc : 0<(half c s)^2-2*half c s+1/5) : J0 c s<0 ∧ -J0 c s≤s^2/10 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have data := quarter_data c s cp.le cn.1 cn.2.2
  have xp : 0<half c s := div_pos positive (by linarith only [cp])
  have identity : (1+(half c s)^2)*(Q c s-half c s)=
      -(half c s)*((half c s)^2-2*half c s+1/5) := by
    dsimp [Q]
    nlinarith only [data.2.2.2.1,data.2.2.2.2]
  have scaled : (1+(half c s)^2)*(Q c s-half c s)<0 := by
    rw [identity]
    exact neg_lt_zero.mpr (mul_pos xp arc)
  have gap := neg_of_mul_neg_right scaled (show 0≤1+(half c s)^2 by positivity)
  have first := mul_neg_of_pos_of_neg positive gap
  have jidentity : J0 c s=s*(Q c s-half c s) := by
    dsimp [J0,Q]
    linear_combination -(C1092MPPMInwardFinal.BottomAngle.half_identity cn)
  have second := mul_nonneg (sq_nonneg s)
    (show 0≤c+2*s-1 by linarith only [cb.2.2.2.2.1,cn.1])
  have boundIdentity : (1+c)*(s^2/10+J0 c s)=s^2*(c+2*s-1)/2 := by
    dsimp [J0]
    linear_combination (1-s)*cn.2.2
  have weighted : 0≤(1+c)*(s^2/10+J0 c s) := by
    rw [boundIdentity]
    nlinarith only [second]
  have bound := nonneg_of_mul_nonneg_right weighted (show 0<1+c by linarith only [cp])
  exact ⟨by rw [jidentity]; exact first,by linarith only [bound]⟩

private theorem endpoint_first {c s : ℝ} (cn : Normal c s) (small : half c s≤53/500) :
    0<FC c s (15/17) (8/17) := by
  have cb := normal_bounds cn
  let x := half c s
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  have cf : c=cosH x := by
    apply (eq_div_iff (half_den_pos x).ne').mpr
    nlinarith only [data.2.2.2.1]
  have sf : s=sinH x := by
    apply (eq_div_iff (half_den_pos x).ne').mpr
    nlinarith only [data.2.2.2.2]
  have monotone := mul_nonneg (show 0≤53/500-x by exact sub_nonneg.mpr small)
    (show 0≤1574-2740*(x+53/500) by linarith only [small])
  have numerator : 0<150-1574*x+2740*x^2 := by nlinarith only [monotone]
  have identity : 1445*(1+x^2)*FC c s (15/17) (8/17)=150-1574*x+2740*x^2 := by
    rw [cf,sf]
    dsimp [FC,Q,kappa,delta,cosH,sinH]
    field_simp [(half_den_pos x).ne'] <;> ring
  have scaled : 0<1445*(1+x^2)*FC c s (15/17) (8/17) := by rw [identity]; exact numerator
  exact pos_of_mul_pos_right scaled (by positivity)

private theorem endpoint_last {c s : ℝ} (cn : Normal c s) (small : half c s≤53/500) :
    0<FE c s (15/17) (8/17) := by
  have cb := normal_bounds cn
  let x := half c s
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  have cf : c=cosH x := by
    apply (eq_div_iff (half_den_pos x).ne').mpr
    nlinarith only [data.2.2.2.1]
  have sf : s=sinH x := by
    apply (eq_div_iff (half_den_pos x).ne').mpr
    nlinarith only [data.2.2.2.2]
  have bound := C1092MPPMNegativeCrosspointSupport.G01Quartic.bernstein
    9 (-90) 154 (-50) (-220) (53/500) x (by norm_num) data.1 small
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [C1092MPPMNegativeCrosspointSupport.G01Quartic.poly])
  have identity : 85*(1+x^2)^2*FE c s (15/17) (8/17)=
      10-90*x+154*x^2-50*x^3-220*x^4 := by
    rw [cf,sf]
    dsimp [FE,Q,kappa,delta,cosH,sinH]
    field_simp [(half_den_pos x).ne'] <;> ring
  have scaled : 0<85*(1+x^2)^2*FE c s (15/17) (8/17) := by
    dsimp [C1092MPPMNegativeCrosspointSupport.G01Quartic.poly] at bound
    nlinarith only [identity,bound]
  exact pos_of_mul_pos_right scaled (by positivity)

theorem first_margin {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (small : half c s≤53/500) (large : 8/17≤t) : 0<FC c s d t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  let H := (d+15/17)/2
  let T := (t+8/17)/2
  have Hp : 0<H := by dsimp [H]; linarith only [eb.1]
  have Tn : 0≤T := by dsimp [T]; linarith only [en.1]
  have Hh : H≤1 := by dsimp [H]; linarith only [eb.2.1]
  have Th : T≤1 := by dsimp [T]; linarith only [eb.2.2.2.1]
  have order : 0≤H-T := by dsimp [H,T]; linarith only [en.2.1]
  have sum : H+T≤10/7 := by dsimp [H,T]; linarith only [eb.2.2.2.2.2]
  have first := mul_nonneg (mul_nonneg (show 0≤c by linarith only [cb.1]) order)
    (show 0≤1-(3/5)*(H+T) by linarith only [sum])
  have a := mul_nonneg Hp.le (show 0≤1-(3/5)*T by linarith only [Th])
  have b := mul_nonneg Tn (show 0≤1-(3/5)*H by linarith only [Hh])
  have last := mul_nonneg cn.1 (show 0≤H+T-(6/5)*H*T by nlinarith only [a,b])
  have bracket : 0≤c*(H-T)*(1-(3/5)*(H+T))+s*(H+T-(6/5)*H*T) := by
    linarith only [first,last]
  have product := mul_nonneg (sub_nonneg.mpr large) bracket
  have identity : H*(FC c s d t-FC c s (15/17) (8/17))=
      (t-8/17)*(c*(H-T)*(1-(3/5)*(H+T))+s*(H+T-(6/5)*H*T)) := by
    dsimp [H,T,FC,Q,kappa,delta]
    linear_combination ((3/5)*s*((d+15/17)/2)-(3/10)*c*((t+8/17)/2)+
      (c-s)/2-(c+s)*((d+15/17)/2))*en.2.2
  have weighted : 0≤H*(FC c s d t-FC c s (15/17) (8/17)) := by rw [identity]; exact product
  have monotone := nonneg_of_mul_nonneg_right weighted Hp
  have endpoint := endpoint_first cn small
  linarith only [monotone,endpoint]

theorem last_margin {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (small : half c s≤53/500) (large : 8/17≤t) : 0<FE c s d t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have bounds := small_bounds cn small
  let A := 1+s-c*Q c s
  let B := 1-c-s*Q c s
  have An : 97/100<A := by
    have first := mul_nonneg (show 0≤c-97/100 by linarith only [bounds.1])
      (show 0≤c+97/100-1 by linarith only [bounds.1])
    have last := mul_nonneg cn.1 (show 0≤1-(2/5)*c by linarith only [cb.2.1])
    dsimp [A,Q]
    nlinarith only [first,last]
  have Bh : B≤s^2/10 := by
    have first := mul_nonneg (sq_nonneg s)
      (show 0≤c+2*s-1 by linarith only [cb.2.2.2.2.1,cn.1])
    have identity : (1+c)*(s^2/10-B)=s^2*(c+2*s-1)/2 := by
      dsimp [B,Q]
      linear_combination (1-s)*cn.2.2
    have weighted : 0≤(1+c)*(s^2/10-B) := by rw [identity]; nlinarith only [first]
    have result := nonneg_of_mul_nonneg_right weighted (by linarith only [cb.1] : 0<1+c)
    linarith only [result]
  have square := mul_pos (show 0<21/100-s by linarith only [bounds.2])
    (show 0<21/100+s by linarith only [cn.1])
  have Bsmall : B<441/100000 := by nlinarith only [Bh,square]
  have endpointNormal : Normal (15/17:ℝ) (8/17) := by norm_num [Normal]
  have cosine := C977CornerSectorBounds.cosine_order en endpointNormal large
  have order : A*d+B*t≤A*(15/17)+B*(8/17) := by
    by_cases Bn : 0≤B
    · exact CommonCases.UnitCircleChord.decreasing (A:=A) (B:=B)
        (by norm_num : (0:ℝ)<15/17) (by linarith only [eb.1])
        endpointNormal.2.2 en.2.2 endpointNormal.1 en.1 large
        (by linarith only [An]) Bn (by linarith only [An,Bsmall])
    · have first := mul_nonneg (show 0≤A by linarith only [An])
        (sub_nonneg.mpr cosine)
      have last := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr large)
        (show B≤0 by linarith only [Bn])
      nlinarith only [first,last]
  have identity : FE c s d t=1-A*d-B*t := by dsimp [FE,A,B,Q,kappa,delta]; ring
  have aligned : FE c s (15/17) (8/17)=1-A*(15/17)-B*(8/17) := by
    dsimp [FE,A,B,Q,kappa,delta]; ring
  have endpoint := endpoint_last cn small
  linarith only [identity,aligned,order,endpoint]

end
end N12Compact.C1092MPPMInwardSmallThree
