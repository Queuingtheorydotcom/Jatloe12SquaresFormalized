import Compact.Completion.C1092.MPPMInwardPositiveNegativeScalars
import Compact.Completion.CommonCases.UnitCircleChord

/-! POSITIVE-MISSING-INWARD-FAR-ENDING sections 5--6. Exact endpoint
polynomials and finite unit-circle differences cover the whole recipient
arc. Both segment alternatives retain a positive reserve at the axial
central endpoint and at the common half-angle endpoint 1/5.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardPositive.FarScalars
open C977CornerCubic C1092WallProfileScalars C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

def alpha (c s : ℝ) : ℝ := (13/50)*c-(43/500)*s
def gamma (c s : ℝ) : ℝ := (13/50)*s+(43/500)*c
def L0 (c s : ℝ) : ℝ := alpha c s+gamma c s-7059/25000

private def A1 (c s : ℝ) : ℝ := 2-c-s+(43/500)*s^2+(2/5)*c*s
private def B1 (c s : ℝ) : ℝ := 1-c+s+(43/500)*c*s-(2/5)*s^2
private def A2 (c s : ℝ) : ℝ := gamma c s-s*L0 c s
private def B2 (c s : ℝ) : ℝ := gamma c s-c*L0 c s

private theorem transverse_coefficients {c s : ℝ} (cn : Normal c s)
    (small : half c s≤1/5) :
    0≤A1 c s ∧ 0≤B1 c s ∧ 0<A1 c s*(60/109)-B1 c s*(91/109) ∧
      0<1-A1 c s*(91/109)-B1 c s*(60/109) := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  let x := half c s
  have xn : 0≤x := div_nonneg cn.1 (by linarith only [cp])
  have xu : x≤1/5 := small
  have cf : c=cosH x := (NegativeScalars.forms cn).1
  have sf : s=sinH x := (NegativeScalars.forms cn).2
  have cs : 0≤c*s := mul_nonneg cp.le cn.1
  have An : 0≤A1 c s := by
    dsimp [A1]
    nlinarith only [cb.2.2.2.2.2,cs,sq_nonneg s]
  have product := mul_nonneg cn.1
    (show 0≤1-(2/5)*s by linarith only [cb.2.2.2.1])
  have Bn : 0≤B1 c s := by dsimp [B1]; nlinarith only [cb.2.1,product,cs]
  have square : x^2≤1/25 := by
    have bound := mul_nonneg (sub_nonneg.mpr xu)
      (show 0≤1/5+x by linarith only [xn])
    nlinarith only [bound]
  have firstTail := mul_nonneg (sq_nonneg x)
    (show 0≤56060-83587*x-500*x^2 by nlinarith only [xu,square])
  have first : 0<15000-67413*x+56060*x^2-83587*x^3-500*x^4 := by
    nlinarith only [firstTail,xu]
  have derivativeIdentity : 250*(1+x^2)^2*(60*A1 c s-91*B1 c s)=
      15000-67413*x+56060*x^2-83587*x^3-500*x^4 := by
    rw [cf,sf]
    dsimp [A1,B1,cosH,sinH]
    field_simp [(half_den_pos x).ne'] <;> ring
  have derivative : 0<A1 c s*(60/109)-B1 c s*(91/109) := by
    rw [←derivativeIdentity] at first
    have result := pos_of_mul_pos_right first (by positivity)
    linarith only [result]
  have lastTail := mul_nonneg (sq_nonneg x)
    (show 0≤2879-3550*x by linarith only [xu])
  have cubic : 0<750-3380*x+2879*x^2-3550*x^3 := by
    nlinarith only [lastTail,xu]
  have positive := mul_pos (show 0<10*x+3 by linarith only [xn]) cubic
  have endpointIdentity : 13625*(1+x^2)^2*
      (1-A1 c s*(91/109)-B1 c s*(60/109))=
      (10*x+3)*(750-3380*x+2879*x^2-3550*x^3) := by
    rw [cf,sf]
    dsimp [A1,B1,cosH,sinH]
    field_simp [(half_den_pos x).ne'] <;> ring
  have endpoint : 0<1-A1 c s*(91/109)-B1 c s*(60/109) := by
    rw [←endpointIdentity] at positive
    exact pos_of_mul_pos_right positive (by positivity)
  exact ⟨An,Bn,derivative,endpoint⟩

theorem transverse_target {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (small : half c s≤1/5) (large : 60/109≤t) :
    0<1-d-t+NegativeScalars.k c s d t*(1-c-(2/5)*s)+
      NegativeScalars.ell c s d t*(1-(543/500)*s) := by
  have coefficients := transverse_coefficients cn small
  have bound := CommonCases.UnitCircleChord.decreasing
    (c:=(91/109:ℝ)) (s:=(60/109:ℝ)) (d:=d) (t:=t) (A:=A1 c s) (B:=B1 c s)
    (by norm_num) (by linarith only [(normal_bounds en).1]) (by norm_num) en.2.2
    (by norm_num) en.1 large coefficients.1 coefficients.2.1 coefficients.2.2.1.le
  have identity : 1-d-t+NegativeScalars.k c s d t*(1-c-(2/5)*s)+
      NegativeScalars.ell c s d t*(1-(543/500)*s)=1-A1 c s*d-B1 c s*t := by
    dsimp [NegativeScalars.k,NegativeScalars.ell,A1,B1]
    linear_combination -d*cn.2.2
  nlinarith only [bound,identity,coefficients.2.2.2]

private theorem oblique_coefficients {c s : ℝ} (cn : Normal c s)
    (small : half c s≤1/5) :
    0≤A2 c s ∧ 0≤B2 c s ∧ 0<A2 c s*(60/109)-B2 c s*(91/109) ∧
      0<gamma c s-A2 c s*(91/109)-B2 c s*(60/109) := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  let x := half c s
  have xn : 0≤x := div_nonneg cn.1 (by linarith only [cp])
  have xu : x≤1/5 := small
  have cf : c=cosH x := (NegativeScalars.forms cn).1
  have sf : s=sinH x := (NegativeScalars.forms cn).2
  have sine : s≤2/5 := by
    have bound := sine_le_twice_half cn
    linarith only [bound,small]
  have Lcap : L0 c s≤7/50 := by
    dsimp [L0,alpha,gamma]
    linarith only [cb.2.1,sine]
  have weighted := mul_nonneg cn.1 (sub_nonneg.mpr Lcap)
  have Ap : 0<A2 c s := by
    have first := mul_pos cp (by norm_num : (0:ℝ)<43/500)
    dsimp [A2,gamma] at *
    nlinarith only [weighted,first,cn.1]
  have first := mul_pos cp
    (show 0<9209/25000-(173/500)*c by linarith only [cb.2.1])
  have last := mul_nonneg cn.1
    (show 0≤13/50-(87/500)*c by linarith only [cb.2.1])
  have Bidentity : B2 c s=
      c*(9209/25000-(173/500)*c)+s*(13/50-(87/500)*c) := by
    dsimp [B2,L0,alpha,gamma]
    ring
  have Bp : 0<B2 c s := by nlinarith only [Bidentity,first,last]
  have square := mul_nonneg xn (sub_nonneg.mpr xu)
  have derivativePolynomial :
      0<1496169*x^4+690380*x^3-2618300*x^2+197780*x+78131 := by
    nlinarith only [square,pow_nonneg xn 3,pow_nonneg xn 4,xu]
  have derivativeIdentity : 2725000*(1+x^2)^2*
      (A2 c s*(60/109)-B2 c s*(91/109))=
      1496169*x^4+690380*x^3-2618300*x^2+197780*x+78131 := by
    rw [cf,sf]
    dsimp [A2,B2,L0,alpha,gamma,cosH,sinH]
    field_simp [(half_den_pos x).ne'] <;> ring
  have derivative : 0<A2 c s*(60/109)-B2 c s*(91/109) := by
    rw [←derivativeIdentity] at derivativePolynomial
    exact pos_of_mul_pos_right derivativePolynomial (by positivity)
  have squareCap : x^2≤1/25 := by
    have bound := mul_nonneg (sub_nonneg.mpr xu)
      (show 0≤1/5+x by linarith only [xn])
    nlinarith only [bound]
  have cubicCap : x^3≤x/25 := by
    have bound := mul_le_mul_of_nonneg_right squareCap xn
    nlinarith only [bound]
  have positiveLinear := mul_nonneg xn
    (show (0:ℝ)≤132781-1963519/25 by norm_num)
  have endpointPolynomial :
      0<516420*x^4-1963519*x^3+272700*x^2+132781*x+2580 := by
    nlinarith only [cubicCap,positiveLinear,sq_nonneg x,pow_nonneg xn 4]
  have endpointIdentity : 1362500*(1+x^2)^2*
      (gamma c s-A2 c s*(91/109)-B2 c s*(60/109))=
      516420*x^4-1963519*x^3+272700*x^2+132781*x+2580 := by
    rw [cf,sf]
    dsimp [A2,B2,L0,alpha,gamma,cosH,sinH]
    field_simp [(half_den_pos x).ne'] <;> ring
  have endpoint : 0<gamma c s-A2 c s*(91/109)-B2 c s*(60/109) := by
    rw [←endpointIdentity] at endpointPolynomial
    exact pos_of_mul_pos_right endpointPolynomial (by positivity)
  exact ⟨Ap.le,Bp.le,derivative,endpoint⟩

theorem oblique_target {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (small : half c s≤1/5) (large : 60/109≤t) :
    0<gamma c s*(1-d-t)+NegativeScalars.ell c s d t*L0 c s := by
  have coefficients := oblique_coefficients cn small
  have bound := CommonCases.UnitCircleChord.decreasing
    (c:=(91/109:ℝ)) (s:=(60/109:ℝ)) (d:=d) (t:=t) (A:=A2 c s) (B:=B2 c s)
    (by norm_num) (by linarith only [(normal_bounds en).1]) (by norm_num) en.2.2
    (by norm_num) en.1 large coefficients.1 coefficients.2.1 coefficients.2.2.1.le
  have identity : gamma c s*(1-d-t)+NegativeScalars.ell c s d t*L0 c s=
      gamma c s-A2 c s*d-B2 c s*t := by
    dsimp [NegativeScalars.ell,A2,B2]
    ring
  nlinarith only [bound,identity,coefficients.2.2.2]

end
#print axioms transverse_target
#print axioms oblique_target
end N12Compact.C1092MPPMInwardPositive.FarScalars
