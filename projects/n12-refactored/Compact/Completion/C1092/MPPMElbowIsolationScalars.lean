import Compact.Completion.C1092.MMMP.UpperThirdScalars

/-! Exact simplifications of NONORDINARY-ISOLATION (9), (11), (13),
(15). The two unit-frame identities turn all four displayed derivative
arguments into nonnegative products, on the complete closed angle orders. -/
namespace N12Compact.C1092MPPMElbowScalars
open C977CornerCubic
set_option Elab.async false
noncomputable section

def kappa (c s d t : ℝ) : ℝ := c*d+s*t
def sigma (c s d t : ℝ) : ℝ := c*t-s*d

theorem frames {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t) :
    7/10<kappa c s d t ∧ kappa c s d t≤1 ∧
      0≤kappa c s d t+sigma c s d t ∧ 0≤kappa c s d t-sigma c s d t ∧
      kappa c s d t*t-sigma c s d t*d=s ∧
      kappa c s d t*s+sigma c s d t*c=t ∧
      kappa c s d t*c-sigma c s d t*s=d ∧
      sigma c s d t≤t := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  have rel := C1092MMMPUpperThirdScalars.relative_bounds cn dn
  have plus : 0≤kappa c s d t+sigma c s d t := by
    have first := mul_nonneg (show 0≤d by linarith only [db.1])
      (sub_nonneg.mpr cn.2.1)
    have last := mul_nonneg dn.1 (show 0≤c+s by linarith only [cb.1,cn.1])
    dsimp [kappa,sigma]
    nlinarith only [first,last]
  have minus : 0≤kappa c s d t-sigma c s d t := by
    have first := mul_nonneg (sub_nonneg.mpr dn.2.1)
      (show 0≤c by linarith only [cb.1])
    have last := mul_nonneg cn.1 (show 0≤d+t by linarith only [db.1,dn.1])
    dsimp [kappa,sigma]
    nlinarith only [first,last]
  have first : kappa c s d t*t-sigma c s d t*d=s := by
    dsimp [kappa,sigma]
    linear_combination s*dn.2.2
  have second : kappa c s d t*s+sigma c s d t*c=t := by
    dsimp [kappa,sigma]
    linear_combination t*cn.2.2
  have third : kappa c s d t*c-sigma c s d t*s=d := by
    dsimp [kappa,sigma]
    linear_combination d*cn.2.2
  have cap : sigma c s d t≤t := by
    have first := mul_nonneg (sub_nonneg.mpr cb.2.1) dn.1
    have last := mul_nonneg cn.1 (show 0≤d by linarith only [db.1])
    dsimp [sigma]
    nlinarith only [first,last]
  refine ⟨?_,?_,plus,minus,first,second,third,cap⟩ <;>
    dsimp [kappa] <;> nlinarith only [rel.1,rel.2.2.1]

def F0 (c s d t : ℝ) : ℝ :=
  1-c-(2/5)*s+(kappa c s d t+sigma c s d t)*(1-d)+
    (2/5)*(kappa c s d t-sigma c s d t)*t

def F1 (c s d t : ℝ) : ℝ :=
  1+kappa c s d t+sigma c s d t-d+(2/5)*t-
    (kappa c s d t+sigma c s d t)*c-
    (2/5)*(kappa c s d t-sigma c s d t)*s

def F2 (c s d t : ℝ) : ℝ :=
  1-c-(2/5)*s+kappa c s d t*(1-d+(2/5)*t)-sigma c s d t*(1+(13/50)*t)

def F3 (c s d t : ℝ) : ℝ :=
  1+kappa c s d t-sigma c s d t-d+(2/5)*t-
    kappa c s d t*c-(2/5)*kappa c s d t*s+(7/20)*sigma c s d t*(c+s)

theorem first_nonnegative {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (order : 0≤sigma c s d t) : 0≤F0 c s d t := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  have f := frames cn dn
  have first := mul_nonneg f.2.2.1 (sub_nonneg.mpr db.2.1)
  have last := mul_nonneg order (sub_nonneg.mpr dn.2.1)
  have identity : F0 c s d t=1-c+(kappa c s d t+sigma c s d t)*(1-d)+
      (2/5)*sigma c s d t*(d-t) := by
    dsimp [F0]
    nlinarith only [f.2.2.2.2.1]
  rw [identity]
  nlinarith only [first,last,cb.2.1]

theorem second_nonnegative {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (order : 0≤sigma c s d t) : 0≤F1 c s d t := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  have f := frames cn dn
  have first := mul_nonneg f.2.2.1 (sub_nonneg.mpr cb.2.1)
  have last := mul_nonneg order (show 0≤c+s by linarith only [cb.1,cn.1])
  have identity : F1 c s d t=1-d+(kappa c s d t+sigma c s d t)*(1-c)+
      (2/5)*sigma c s d t*(c+s) := by
    dsimp [F1]
    nlinarith only [f.2.2.2.2.2.1]
  rw [identity]
  nlinarith only [first,last,db.2.1]

theorem third_nonnegative {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (order : sigma c s d t≤0) : 0≤F2 c s d t := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  have f := frames cn dn
  have first := mul_nonneg (show 0≤kappa c s d t by linarith only [f.1])
    (sub_nonneg.mpr db.2.1)
  have last := mul_nonneg (neg_nonneg.mpr order)
    (show 0≤1-(2/5)*d+(13/50)*t by linarith only [db.2.1,dn.1])
  have identity : F2 c s d t=1-c+kappa c s d t*(1-d)-
      sigma c s d t*(1-(2/5)*d+(13/50)*t) := by
    dsimp [F2]
    nlinarith only [f.2.2.2.2.1]
  rw [identity]
  nlinarith only [first,last,cb.2.1]

theorem fourth_nonnegative {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (small : s≤7/25) (order : sigma c s d t≤0) : 0≤F3 c s d t := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  have f := frames cn dn
  have first := mul_nonneg (show 0≤kappa c s d t by linarith only [f.1])
    (sub_nonneg.mpr cb.2.1)
  have last := mul_nonneg (neg_nonneg.mpr order)
    (show 0≤1-(3/4)*c-(7/20)*s by linarith only [cb.2.1,small])
  have identity : F3 c s d t=1-d+kappa c s d t*(1-c)-
      sigma c s d t*(1-(3/4)*c-(7/20)*s) := by
    dsimp [F3]
    nlinarith only [f.2.2.2.2.2.1]
  rw [identity]
  nlinarith only [first,last,db.2.1]

#print axioms first_nonnegative
#print axioms fourth_nonnegative
end N12Compact.C1092MPPMElbowScalars
