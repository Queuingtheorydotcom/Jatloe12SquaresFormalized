import Compact.Completion.C1092.MPPMNegativeCrosspointG01Quartic
import Compact.Completion.C1092.MPPMNegativeOwnedPositiveCeilingScalars

/-! NEGATIVE-MISSING-POSITIVE-CEILING §§3--7. Exact full-interval
inequalities, with the genuine 1.086 predecessor cap. The printed
concavity calculation is replaced by five rational Bernstein bounds. -/
namespace N12Compact.C1092MPPMNegativeMissingPositiveCeiling.Scalars
open C977CornerCubic C1092ShallowPositiveScalars C1092MPPMNonpositivePredecessor
set_option Elab.async false
noncomputable section

def P0 (b r : ℝ) := b+r-13/50-(21/25)*b*r
def Q0 (b r : ℝ) := b-r-(13/50)*r^2-(11/10)*b^2
def P1 (c s : ℝ) := 11/10-c+c^2-(7/50)*c*s
def Q1 (c s : ℝ) := s-c*s+13/50+(7/50)*s^2
def f2 (b r : ℝ) := 1+b*r-b-r+(43/500)*b^2
def g2 (b r : ℝ) := b^2-b+r-(43/500)*b*r
def quartic (x : ℝ) := -10847*x^4-4770*x^3+4344*x^2+770*x-347

theorem own_margin {c s b r : ℝ} (cn : Normal c s) (wn : Normal b r)
    (bh : b<33/40) (rl : 283/500<r) : 0<c*P0 b r+s*Q0 b r := by
  have cb := normal_bounds cn
  have wb := normal_bounds wn
  have cp : 0<c := by linarith only [cb.1]
  have squareOrder := mul_nonneg (sub_nonneg.mpr wn.2.1)
    (show 0≤b+r by linarith only [wb.1,wn.1])
  have qneg : Q0 b r<0 := by
    dsimp [Q0]
    nlinarith only [bh,rl,squareOrder,wn.2.2,sq_nonneg r]
  have sumIdentity : P0 b r+Q0 b r=2*b-13/25-(21/25)*b*(b+r) := by
    dsimp [P0,Q0]
    linear_combination -(13/50)*wn.2.2
  have hcap := mul_nonneg (show 0≤b by linarith only [wb.1])
    (show 0≤10/7-(b+r) by linarith only [wb.2.2.2.2.2])
  have sum : 0<P0 b r+Q0 b r := by
    nlinarith only [sumIdentity,hcap,wb.1]
  have first := mul_pos cp sum
  have last := mul_nonneg (sub_nonneg.mpr cn.2.1) (neg_nonneg.mpr qneg.le)
  nlinarith only [first,last]

theorem coefficient_bounds {b r : ℝ} (wn : Normal b r)
    (bh : b<33/40) (product : 23/50<b*r) : f2 b r<29/200 ∧ g2 b r<461/1000 := by
  have wb := normal_bounds wn
  have bp : 0<b := by linarith only [wb.1]
  have Hn : 1≤b+r := wb.2.2.2.2.1
  have Hh : b+r≤283/200 := by
    nlinarith only [wn.2.2,sq_nonneg (b-r),sq_nonneg (b+r-283/200)]
  have square := mul_nonneg (sub_nonneg.mpr Hh)
    (show 0≤b+r+283/200-2 by linarith only [Hn])
  have bSquare := mul_pos (show 0<33/40-b by linarith only [bh])
    (show 0<33/40+b by linarith only [bp])
  have old := mul_nonneg (sub_nonneg.mpr wn.2.1)
    (show 0≤2-b-r by linarith only [Hh])
  constructor
  · dsimp [f2]
    nlinarith only [square,bSquare,wn.2.2]
  · dsimp [g2]
    nlinarith only [old,product,wn.2.2]

theorem quartic_positive {x : ℝ} (xl : 7/24≤x) (xu : x≤5/12) : 0<quartic x := by
  let l : ℝ := 7/24
  let a0 := quartic l-1
  let a1 := -43388*l^3-14310*l^2+8688*l+770
  let a2 := -65082*l^2-14310*l+4344
  let a3 := -43388*l-4770
  have bound := C1092MPPMNegativeCrosspointSupport.G01Quartic.bernstein
    a0 a1 a2 a3 (-10847) (1/8) (x-l) (by norm_num)
    (by dsimp [l]; linarith only [xl]) (by dsimp [l]; linarith only [xu])
    (by norm_num [a0,l,quartic]) (by norm_num [a0,a1,l,quartic])
    (by norm_num [a0,a1,a2,l,quartic]) (by norm_num [a0,a1,a2,a3,l,quartic])
    (by norm_num [a0,a1,a2,a3,l,quartic,C1092MPPMNegativeCrosspointSupport.G01Quartic.poly])
  have identity : C1092MPPMNegativeCrosspointSupport.G01Quartic.poly
      a0 a1 a2 a3 (-10847) (x-l)=quartic x-1 := by
    dsimp [a0,a1,a2,a3,quartic,C1092MPPMNegativeCrosspointSupport.G01Quartic.poly]
    ring
  rw [identity] at bound
  linarith only [bound]

theorem last_margin {c s b r : ℝ} (cn : Normal c s) (wn : Normal b r)
    (large : 7/24≤s/(1+c)) : 0<1-P1 c s*b-Q1 c s*r := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  let x := s/(1+c)
  have data := C1092WallProfileScalars.quarter_data c s cp.le cn.1 cn.2.2
  have xu : x≤5/12 := by
    have weight := mul_nonneg (sub_nonneg.mpr cn.2.1) (show 0≤1+x^2 by positivity)
    have quadratic : x^2+2*x≤1 := by
      nlinarith only [weight,data.2.2.2.1,data.2.2.2.2]
    by_contra no
    have gap := mul_pos (show 0<x-5/12 by linarith only [no])
      (show 0<x+5/12+2 by linarith only [data.1])
    nlinarith only [gap,quadratic]
  have cform : c=cosH x := by
    apply (eq_div_iff (half_den_pos x).ne').mpr
    nlinarith only [data.2.2.2.1]
  have sform : s=sinH x := by
    apply (eq_div_iff (half_den_pos x).ne').mpr
    nlinarith only [data.2.2.2.2]
  have identity : 1250*(1+x^2)^2*(1-(P1 c s)^2-(Q1 c s)^2)=quartic x := by
    rw [cform,sform]
    dsimp [P1,Q1,quartic,cosH,sinH]
    field_simp [(half_den_pos x).ne'] <;> ring
  have positive := quartic_positive large xu
  have weighted : 0<1250*(1+x^2)^2*(1-(P1 c s)^2-(Q1 c s)^2) := by
    rw [identity]; exact positive
  have norm : (P1 c s)^2+(Q1 c s)^2<1^2 := by
    have result := pos_of_mul_pos_right weighted
      (show 0≤1250*(1+x^2)^2 by positivity)
    linarith only [result]
  have bound := norm_lt (P1 c s) (Q1 c s) b r 1 wn.2.2 (by norm_num) norm
  linarith only [bound]

theorem transverse_margin {c s : ℝ} (cn : Normal c s)
    (large : 7/24≤s/(1+c)) : (229/200)*c+(61/1000)*s<1 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  let x := s/(1+c)
  have data := C1092WallProfileScalars.quarter_data c s cp.le cn.1 cn.2.2
  have order : 336/625≤s := by
    have weight := mul_nonneg (show 0≤x-7/24 by exact sub_nonneg.mpr large)
      (show 0≤2-(336/625)*(x+7/24) by linarith only [data.2.1])
    have result : 0≤(1+x^2)*(s-336/625) := by
      nlinarith only [data.2.2.2.2,weight]
    have positive : 0<1+x^2 := by positivity
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right result positive)
  have bound := CommonCases.UnitCircleChord.decreasing
    (c := (527/625:ℝ)) (s := (336/625:ℝ)) (d := c) (t := s)
    (A := (229/200:ℝ)) (B := (61/1000:ℝ)) (by norm_num) cp.le
    (by norm_num) cn.2.2 (by norm_num) cn.1 order
    (by norm_num) (by norm_num) (by norm_num)
  linarith only [bound]

end
end N12Compact.C1092MPPMNegativeMissingPositiveCeiling.Scalars
