import Compact.Completion.C1092.MPPMPositiveNegativeRetainingScalars
import Compact.Completion.C1092.WallProfileScalars
import Compact.Geometry.C1092ShallowPositiveScalars

/-! NEGATIVE-OWNED-POSITIVE-CEILING, exact full-arc scalar margins.
The only quartic is bounded by one rational coefficient estimate on
the whole half-angle interval [11/100,5/12]. Source only. -/
namespace N12Compact.C1092MPPMNegativeOwnedPositiveCeiling.Scalars
open C977CornerCubic C1092ShallowPositiveScalars C1092MPPMNonpositivePredecessor
set_option Elab.async false
noncomputable section

def P0 (b r : ℝ) : ℝ := b+r-13/50-(7/20)*b^2-(13/20)*b*r
def Q0 (b r : ℝ) : ℝ := b-r-b^2+(7/20)*r*(b-r)
def P1 (c s : ℝ) : ℝ := 1-c+c^2-(7/50)*c*s
def Q1 (c s : ℝ) : ℝ := s-c*s+13/50+(7/50)*s^2
def quartic (x : ℝ) : ℝ := -20169*x^4-9400*x^3+8738*x^2+1400*x-169

theorem own_margin {c s b r : ℝ} (cn : Normal c s) (wn : Normal b r)
    (close : 87/100<b) : 0<c*P0 b r+s*Q0 b r := by
  have cb := normal_bounds cn
  have wb := normal_bounds wn
  have cp : 0<c := by linarith only [cb.1]
  have rn := wn.1
  have qlow : Q0 b r≤0 := by
    have a := mul_nonneg rn (show 0≤1-b+r by linarith only [wb.2.1,rn])
    have tail := mul_nonneg rn (show 0≤13/20-r/2 by linarith only [wb.2.2.2.1])
    dsimp [Q0]
    nlinarith only [a,tail,wn.2.2,sq_nonneg (1-b)]
  have br : b*r≤1/2 := by nlinarith only [wn.2.2,sq_nonneg (b-r)]
  have square := mul_pos (show 0<13/100-(1-b) by linarith only [close])
    (show 0<13/100+(1-b) by linarith only [wb.2.1])
  have sumIdentity : P0 b r+Q0 b r=2*b-61/100-b^2-(3/10)*b*r := by
    dsimp [P0,Q0]
    linear_combination -(7/20)*wn.2.2
  have sum : 11/50<P0 b r+Q0 b r := by
    nlinarith only [square,br,sumIdentity]
  have cone := mul_nonneg (sub_nonneg.mpr cn.2.1) (neg_nonneg.mpr qlow)
  have weighted := mul_pos cp (show 0<P0 b r+Q0 b r by linarith only [sum])
  nlinarith only [cone,weighted]

theorem quartic_positive {x : ℝ} (xl : 11/100≤x) (xu : x≤5/12) : 0<quartic x := by
  have xn : 0≤x := by linarith only [xl]
  have squareHigh := mul_nonneg (sub_nonneg.mpr xu)
    (show 0≤5/12+x by linarith only [xn])
  have coefficient : 1250≤8738-9400*x-20169*x^2 := by
    nlinarith only [xu,squareHigh]
  have weighted := mul_nonneg (sub_nonneg.mpr coefficient) (sq_nonneg x)
  have squareLow := mul_nonneg (sub_nonneg.mpr xl)
    (show 0≤x+11/100 by linarith only [xn])
  dsimp [quartic]
  nlinarith only [weighted,squareLow,xl]

theorem last_margin {c s b r : ℝ} (cn : Normal c s) (wn : Normal b r)
    (large : 11/100≤s/(1+c)) : 0<1-P1 c s*b-Q1 c s*r := by
  have cb := normal_bounds cn
  have cs := C1092MPPMPositiveRetainingSteep.Scalars.canonical_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  let x := s/(1+c)
  have den : 0<1+c := by linarith only [cp]
  have xl : 11/100≤x := large
  have xu : x≤5/12 := by
    apply (div_le_iff₀ den).mpr
    linarith only [cn.2.1,cs.2.2.2.1]
  have data := C1092WallProfileScalars.quarter_data c s cp.le cn.1 cn.2.2
  have cform : c=cosH x := by
    apply (eq_div_iff (half_den_pos x).ne').mpr
    have identity : (1+x^2)*c=1-x^2 := data.2.2.2.1
    nlinarith only [identity]
  have sform : s=sinH x := by
    apply (eq_div_iff (half_den_pos x).ne').mpr
    have identity : (1+x^2)*s=2*x := data.2.2.2.2
    nlinarith only [identity]
  have identity : 2500*(1+x^2)^2*(1-(P1 c s)^2-(Q1 c s)^2)=quartic x := by
    rw [cform,sform]
    dsimp [P1,Q1,quartic,cosH,sinH]
    field_simp [(half_den_pos x).ne']
    <;> ring
  have positive := quartic_positive xl xu
  have scaled : 0<2500*(1+x^2)^2*(1-(P1 c s)^2-(Q1 c s)^2) := by
    rw [identity]
    exact positive
  have norm : (P1 c s)^2+(Q1 c s)^2<1^2 := by
    have result := pos_of_mul_pos_right scaled
      (show 0≤2500*(1+x^2)^2 by positivity)
    linarith only [result]
  have bound := norm_lt (P1 c s) (Q1 c s) b r 1 wn.2.2 (by norm_num) norm
  linarith only [bound]

end
end N12Compact.C1092MPPMNegativeOwnedPositiveCeiling.Scalars
