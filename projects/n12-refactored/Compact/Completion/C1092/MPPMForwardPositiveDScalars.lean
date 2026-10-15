import Compact.Completion.CommonCases.CanonicalScalars

/-! The two exact coefficient regimes in C1092-POSITIVE-D-TRANSFER.
The rational sum bound 10/7 replaces the chapter's square-root estimate.
All statements include zero sine and the diagonal endpoint. Uncompiled. -/
namespace N12Compact.C1092MPPMForwardPositiveD
set_option Elab.async false

def coeffA (c s f : ℝ) : ℝ := c*(c+(3/2)*s)-s*f+c+s-2
def coeffB (c s f : ℝ) : ℝ := -s*(c+(3/2)*s)-c*f+c-s+87/50

structure Coefficients (c s f : ℝ) : Prop where
  first : 0≤coeffA c s f
  second : coeffB c s f≤37/50
  coupled : 0<coeffA c s f*s+coeffB c s f*c
  short : f-((87/50)*c-2*s)<1

theorem regime_one (c s : ℝ) (cp : 0<c) (sn : 0≤s) (order : s≤c)
    (unit : c^2+s^2=1) (shallow : 200*s<43*c) :
    Coefficients c s ((113/50)*c-s) := by
  have cb := CommonCases.CanonicalScalars.bounds c s cp sn order unit
  have su : s<43/200 := by linarith only [shallow,cb.2.1]
  have square := mul_pos (sub_pos.mpr su)
    (show 0<43/200+s by linarith only [sn])
  have cl : 97/100<c := by nlinarith only [unit,square,cp]
  have aEq : coeffA c s ((113/50)*c-s)=c+s-1-(19/25)*c*s := by
    dsimp only [coeffA]
    linear_combination unit
  have bEq : coeffB c s ((113/50)*c-s)=c-s-(19/25)*c^2+6/25 := by
    dsimp only [coeffB]
    linear_combination -(3/2)*unit
  have product := mul_nonneg cp.le sn
  have aNonneg : 0≤coeffA c s ((113/50)*c-s) := by
    rw [aEq]
    linarith only [cb.2.2.2.2,product]
  have bPositive : 0<coeffB c s ((113/50)*c-s) := by
    rw [bEq]
    nlinarith only [unit,sq_nonneg s,cl,su]
  refine ⟨aNonneg,?_,?_,?_⟩
  · rw [bEq]
    nlinarith only [sq_nonneg (c-1),sq_nonneg c,sn]
  · exact add_pos_of_nonneg_of_pos (mul_nonneg aNonneg sn) (mul_pos bPositive cp)
  · linarith only [cb.2.1,su]

theorem regime_two (c s : ℝ) (cp : 0<c) (sn : 0≤s) (order : s≤c)
    (unit : c^2+s^2=1) : Coefficients c s (2*c-(457/500)*s) := by
  have cb := CommonCases.CanonicalScalars.bounds c s cp sn order unit
  have product := mul_nonneg cp.le sn
  have ordered := mul_nonneg sn (sub_nonneg.mpr order)
  have aEq : coeffA c s (2*c-(457/500)*s)=
      c+s-1-(1/2)*c*s-(43/500)*s^2 := by
    dsimp only [coeffA]
    linear_combination unit
  have bEq : coeffB c s (2*c-(457/500)*s)=
      c-s-(1/2)*c^2-(43/500)*c*s+6/25 := by
    dsimp only [coeffB]
    linear_combination -(3/2)*unit
  have short : (13/50)*c+(543/500)*s<1 := by
    linarith only [cb.2.2.2.1,order]
  have identity : coeffA c s (2*c-(457/500)*s)*s+
      coeffB c s (2*c-(457/500)*s)*c = 1-(13/50)*c-(543/500)*s := by
    dsimp only [coeffA,coeffB]
    linear_combination (1-(2*c-(457/500)*s))*unit
  refine ⟨?_,?_,?_,?_⟩
  · rw [aEq]
    nlinarith only [cb.2.2.2.2,product,ordered]
  · rw [bEq]
    nlinarith only [sq_nonneg (c-1),sn,product]
  · rw [identity]
    linarith only [short]
  · linarith only [short]

end N12Compact.C1092MPPMForwardPositiveD
