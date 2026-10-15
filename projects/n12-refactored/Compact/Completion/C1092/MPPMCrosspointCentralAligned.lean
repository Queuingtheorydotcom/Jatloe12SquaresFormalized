import Compact.Completion.C1092.MPPMCrosspointSupportScalars
import Compact.Completion.C1092.MPPMPositiveRetainingSteepScalars
import Compact.Completion.CommonCases.UnitCircleChord

/-! STEEP-POSITIVE-CENTRAL-SCALAR §§1--2. The diagonal minimum and both
orders of the beta=p endpoint use finite unit-circle differences. No
derivatives, angle samples or strict endpoint exclusions are used. -/
namespace N12Compact.C1092MPPMCrosspointSupport.Central
open C977CornerCubic C977CornerSectorBounds
open C1092MPPMPositiveRetainingSteep.Scalars
set_option Elab.async false
noncomputable section

def diagonalValue (c s : ℝ) : ℝ :=
  2*(c+s)-2-(1043/500)*c*s+(14/25)*s^2

theorem diagonal_lower {c s : ℝ} (cn : Normal c s) (steep : 3/5≤s) :
    1/3125≤diagonalValue c s := by
  have cb := normal_bounds cn
  have arc := steep_bounds cn steep
  have cp : 0<c := by linarith only [cb.1]
  let J := 2*(c+4/5-s-3/5)-
    (1043/500)*(c*(c+4/5)-(3/5)*(s+3/5))+
    (14/25)*(s+3/5)*(c+4/5)
  have square := mul_nonneg (show 0≤4/5-c by linarith only [arc.1])
    (show 0≤4/5+c by linarith only [cp])
  have first := mul_nonneg (show 0≤s-3/5 by linarith only [steep])
    (show 0≤c+4/5 by linarith only [cp])
  have last := mul_nonneg (by norm_num : (0:ℝ)≤6/5)
    (show 0≤c-7/10 by linarith only [cb.1])
  have bracket : 0≤J := by
    dsimp [J]
    nlinarith only [square,first,last,cn.2.1,steep,arc.1]
  have product := mul_nonneg (show 0≤s-3/5 by linarith only [steep]) bracket
  have identity : (c+4/5)*(diagonalValue c s-1/3125)=(s-3/5)*J := by
    dsimp [diagonalValue,J]
    linear_combination (1871/2500)*cn.2.2
  have weighted : 0≤(c+4/5)*(diagonalValue c s-1/3125) := by
    rw [identity]; exact product
  have result := nonneg_of_mul_nonneg_right weighted (show 0<c+4/5 by linarith only [cp])
  linarith only [result]

theorem aligned_C {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) : 1/3125≤G00 c s d t c s := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have small := canonical_bounds cn
  have arc := steep_bounds cn steep
  have cp : 0<c := by linarith only [cb.1]
  have dp : 0<d := by linarith only [eb.1]
  have sp : 0<s := by linarith only [steep]
  have base := diagonal_lower cn steep
  by_cases order : t≤s
  · let A := 2*c+(1043/500)*s-c*s-2
    let B := s*(36/25-s)
    have An : 0≤A := by
      dsimp [A]
      nlinarith only [cb.1,steep,cn.2.2,sq_nonneg (c-s)]
    have Bn : 0≤B := mul_nonneg cn.1
      (by linarith only [small.2.2.2.1])
    have derivative : 0≤B*c-A*s := by
      have bound : 0≤2-(14/25)*c-(1043/500)*s := by
        linarith only [small.2.2.2.2,cn.2.1]
      have product := mul_nonneg cn.1 bound
      dsimp [A,B]
      nlinarith only [product]
    have comparison := CommonCases.UnitCircleChord.increasing cp dp.le
      cn.2.2 en.2.2 cn.1 en.1 order An Bn derivative
    have de : 0≤d*s-t*c := by
      have cross := CommonCases.UnitCircleChord.cross_order dp.le cp.le
        en.2.2 cn.2.2 en.1 cn.1 order
      nlinarith only [cross]
    have form : G00 c s d t c s=s-A*d-B*t := by
      dsimp [G00,k,kC,kE,deltaC,deltaE,C0,E0]
      rw [show c*s-s*c=0 by ring,abs_zero,abs_of_nonneg de]
      dsimp [A,B]
      linear_combination d*cn.2.2
    have self : s-A*c-B*s=diagonalValue c s := by
      dsimp [A,B,diagonalValue]
      linear_combination (s-2)*cn.2.2
    rw [form]
    linarith only [comparison,self,base]
  · have order : s≤t := (lt_of_not_ge order).le
    let A := 2*c+(1043/500)*s-1-c*(c+s)
    let B := s*(36/25-c-s)
    have product := mul_nonneg (show 0≤4/5-c by linarith only [arc.1])
      (show 0≤c+s by linarith only [cp,cn.1])
    have An : 0≤A := by
      dsimp [A]
      nlinarith only [cb.1,steep,small.2.2.2.2,product]
    have Bn : 0≤B := mul_nonneg cn.1
      (by linarith only [small.2.2.2.2])
    have derivative : 0≤A*s-B*c := by
      have bound : 0≤(14/25)*c+(1043/500)*s-1 := by
        linarith only [cp,steep]
      have product := mul_nonneg cn.1 bound
      dsimp [A,B]
      nlinarith only [product]
    have comparison := CommonCases.UnitCircleChord.decreasing cp dp.le
      cn.2.2 en.2.2 cn.1 en.1 order An Bn derivative
    have de : d*s-t*c≤0 := by
      have cross := CommonCases.UnitCircleChord.cross_order cp.le dp.le
        cn.2.2 en.2.2 cn.1 en.1 order
      nlinarith only [cross]
    have form : G00 c s d t c s=s-A*d-B*t := by
      dsimp [G00,k,kC,kE,deltaC,deltaE,C0,E0]
      rw [show c*s-s*c=0 by ring,abs_zero,abs_of_nonpos de]
      dsimp [A,B]
      ring
    have self : s-A*c-B*s=diagonalValue c s := by
      dsimp [A,B,diagonalValue]
      linear_combination (c+s-2)*cn.2.2
    rw [form]
    linarith only [comparison,self,base]

end
end N12Compact.C1092MPPMCrosspointSupport.Central
