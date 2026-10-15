import Compact.Completion.C1092.MPPMInwardPositiveSuccessor
import Compact.Completion.C1092.MPPMCrosspointBoundaryHalf

/-! Shared positive-C/negative-E comparisons and the two complete
central ranges in POSITIVE-MISSING-INWARD-ORIGIN-ENDING. Tight rational
canonical sums and exact norm polynomials replace angular calculus. -/
namespace N12Compact.C1092MPPMInwardPositive.NegativeScalars
open C977CornerCubic C1092WallProfileScalars C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

def k (c s d t : ℝ) : ℝ := c*d-s*t
def ell (c s d t : ℝ) : ℝ := c*t+s*d
def smallA (c s : ℝ) : ℝ := 2-c-s+(2/5)*c*s
def smallB (c s : ℝ) : ℝ := 1-c+s-(2/5)*s^2

theorem tight_sum {c s : ℝ} (cn : Normal c s) : c+s≤99/70 := by
  have cb := normal_bounds cn
  apply le_of_not_gt
  intro high
  have product := mul_pos (sub_pos.mpr high)
    (show 0<c+s+99/70 by linarith only [cb.1,cn.1])
  nlinarith only [product,cn.2.2,sq_nonneg (c-s)]

theorem relative {c s d t : ℝ} (cn : Normal c s) (strictOrder : s<c)
    (positive : 0<s) (en : Normal d t) :
    0<k c s d t ∧ 0<ell c s d t ∧ k c s d t≤1 ∧ ell c s d t≤1 := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  have first := mul_pos (sub_pos.mpr strictOrder) dp
  have last := mul_nonneg cn.1 (sub_nonneg.mpr en.2.1)
  have kp : 0<k c s d t := by dsimp [k]; nlinarith only [first,last]
  have first' := mul_nonneg (show 0≤c by linarith only [cb.1]) en.1
  have last' := mul_pos positive dp
  have lp : 0<ell c s d t := by dsimp [ell]; nlinarith only [first',last']
  have unit : (k c s d t)^2+(ell c s d t)^2=1 := by
    dsimp [k,ell]
    linear_combination (d^2+t^2)*cn.2.2+en.2.2
  refine ⟨kp,lp,?_,?_⟩ <;>
    nlinarith only [unit,sq_nonneg (k c s d t),sq_nonneg (ell c s d t),
      sq_nonneg (k c s d t-1),sq_nonneg (ell c s d t-1)]

theorem downward {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (kn : 0≤k c s d t) (kh : k c s d t≤1)
    (lh : ell c s d t≤1) :
    0<1-(7/20)*(c+s)+k c s d t*(1-(543/500)*d)+ell c s d t*(1-d-t) := by
  have eb := normal_bounds en
  have cs := tight_sum cn
  have es := tight_sum en
  have sum := C1092MPPMActualNonordinary.normal_sum d t en
  have first := mul_nonneg kn (show 0≤1-d by linarith only [eb.2.1])
  have productCap : k c s d t*d≤1 := by nlinarith only [first,kh]
  have last := mul_nonneg (show 0≤1-ell c s d t by linarith only [lh])
    (show 0≤d+t-1 by linarith only [sum.1])
  nlinarith only [cs,es,first,productCap,last]

theorem transverse {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (kn : 0≤k c s d t) (ln : 0≤ell c s d t) (lh : ell c s d t≤1) :
    0<1+(k c s d t+ell c s d t)*(1-c)+
      (2/5)*(k c s d t-ell c s d t)*s-t+(2/5)*d := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have first := mul_nonneg (add_nonneg kn ln) (show 0≤1-c by linarith only [cb.2.1])
  have last := mul_nonneg (show 0≤k c s d t-ell c s d t+1 by linarith only [kn,lh]) cn.1
  have sum := tight_sum cn
  have order := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤c+s by linarith only [cb.1,cn.1])
  have small : s<71/100 := by
    nlinarith only [order,cn.2.2,cn.1,sq_nonneg (s-71/100)]
  nlinarith only [first,last,small,en.2.1,eb.2.1]

theorem forms {c s : ℝ} (cn : Normal c s) : c=cosH (half c s) ∧ s=sinH (half c s) := by
  have data := quarter_data c s (by linarith only [(normal_bounds cn).1]) cn.1 cn.2.2
  constructor <;> apply (eq_div_iff (half_den_pos (half c s)).ne').mpr <;>
    nlinarith only [data.2.2.2.1,data.2.2.2.2]

theorem small_target {c s d t : ℝ} (cn : Normal c s) (positive : 0<s)
    (en : Normal d t) (small : half c s≤1/5) :
    0<1-d-t+k c s d t*(1-c-(2/5)*s)+ell c s d t*(1-s) := by
  let x := half c s
  have xp : 0<x := div_pos positive (by linarith only [(normal_bounds cn).1])
  have coordinate := forms cn
  have tail := mul_nonneg (sq_nonneg x) (show 0≤55-75*x by linarith only [small])
  have polynomial : 0<15-59*x+55*x^2-75*x^3 := by nlinarith only [tail,small]
  have identity : 25*(1+x^2)^2*(1-(smallA c s)^2-(smallB c s)^2)=
      4*x*(15-59*x+55*x^2-75*x^3) := by
    rw [coordinate.1,coordinate.2]
    dsimp [smallA,smallB,cosH,sinH]
    field_simp [(half_den_pos x).ne'] <;> ring
  have scaled : 0<25*(1+x^2)^2*(1-(smallA c s)^2-(smallB c s)^2) := by
    rw [identity]
    exact mul_pos (by linarith only [xp]) polynomial
  have norm : (smallA c s)^2+(smallB c s)^2<1 := by
    have result := pos_of_mul_pos_right scaled (by positivity)
    linarith only [result]
  have dot := C1092MPPMInwardFinal.dot_strict en.2.2 (by norm_num : (0:ℝ)<1)
    (by simpa only [one_pow] using norm)
  have formula : 1-d-t+k c s d t*(1-c-(2/5)*s)+ell c s d t*(1-s)=
      1-smallA c s*d-smallB c s*t := by
    dsimp [k,ell,smallA,smallB]
    linear_combination -d*cn.2.2
  nlinarith only [dot,formula]

theorem marker_norm {c s : ℝ} (cn : Normal c s)
    (low : 1/5≤half c s) (high : half c s≤2/5) :
    (SuccessorScalars.A c s)^2+(SuccessorScalars.B c s)^2<1 := by
  let x := half c s
  have xn : 0≤x := le_trans (by norm_num) low
  have tail := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg xn 3)
    (show 5409*x-2196≤0 by linarith only [high])
  have square := mul_nonneg (show 0≤x-1/5 by linarith only [low])
    (show 0≤x+1/5 by linarith only [xn])
  have polynomial : 5409*x^4-2196*x^3-366*x^2-204*x+49<0 := by
    nlinarith only [tail,square,low]
  have coordinate := forms cn
  have identity : 400*(1+x^2)^2*(1-(SuccessorScalars.A c s)^2-(SuccessorScalars.B c s)^2)=
      -(5409*x^4-2196*x^3-366*x^2-204*x+49) := by
    rw [coordinate.1,coordinate.2]
    dsimp [SuccessorScalars.A,SuccessorScalars.B,cosH,sinH]
    field_simp [(half_den_pos x).ne'] <;> ring
  have scaled : 0<400*(1+x^2)^2*(1-(SuccessorScalars.A c s)^2-(SuccessorScalars.B c s)^2) := by
    rw [identity]
    linarith only [polynomial]
  have result := pos_of_mul_pos_right scaled (by positivity)
  linarith only [result]

theorem marker_target {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (low : 1/5≤half c s) (high : half c s≤2/5) :
    0<1-d-t+k c s d t*(1-c-(2/5)*s)+ell c s d t*(1-(7/20)*(c+s)) := by
  have norm := marker_norm cn low high
  have dot := C1092MPPMInwardFinal.dot_strict en.2.2 (by norm_num : (0:ℝ)<1)
    (by simpa only [one_pow,add_comm] using norm)
  have formula : 1-d-t+k c s d t*(1-c-(2/5)*s)+ell c s d t*(1-(7/20)*(c+s))=
      1-SuccessorScalars.B c s*d-SuccessorScalars.A c s*t := by
    dsimp [k,ell,SuccessorScalars.A,SuccessorScalars.B]
    linear_combination (-d-(7/20)*t)*cn.2.2
  nlinarith only [dot,formula]

end
#print axioms downward
#print axioms small_target
#print axioms marker_target
end N12Compact.C1092MPPMInwardPositive.NegativeScalars
