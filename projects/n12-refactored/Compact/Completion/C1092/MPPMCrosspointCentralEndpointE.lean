import Compact.Completion.C1092.MPPMCrosspointCentralAligned

/-! STEEP-POSITIVE-CENTRAL-SCALAR §3. Both complete angle orders for
beta=q. The two monotonicity arguments and the remaining endpoint
quadratic are exact circle-chord identities; the weak p=q=p0 endpoint
retains the sharp value 1/3125. -/
namespace N12Compact.C1092MPPMCrosspointSupport.Central
open C977CornerCubic C977CornerSectorBounds
open C1092MPPMPositiveRetainingSteep.Scalars
set_option Elab.async false
noncomputable section

private theorem coefficients {d t : ℝ} (en : Normal d t) :
    9/10≤d*(2-d) ∧ -11/20≤2-(1043/500)*d-(36/25)*t+d*t := by
  have eb := normal_bounds en
  have first := mul_nonneg (show 0≤d-7/10 by linarith only [eb.1])
    (show 0≤13/10-d by linarith only [eb.2.1])
  have cross := mul_nonneg (show 0≤d by linarith only [eb.1]) en.1
  have bound : (1043/500)*d+(36/25)*t<51/20 := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg
      (show 0≤(1043/500)*d+(36/25)*t-51/20 by linarith only [bad])
      (show 0≤(1043/500)*d+(36/25)*t+51/20 by linarith only [bad])
    have square := sq_nonneg ((36/25)*d-(1043/500)*t)
    nlinarith only [product,square,en.2.2]
  exact ⟨by nlinarith only [first],by linarith only [bound,cross]⟩

private theorem move_up {c s C S A B : ℝ} (cn : Normal c s) (bn : Normal C S)
    (steep : 3/5≤s) (baseSteep : 3/5≤S) (order : S≤s)
    (An : 9/10≤A) (Bn : -11/20≤B) :
    -A*C+B*S≤-A*c+B*s := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have ca := steep_bounds cn steep
  have ba := steep_bounds bn baseSteep
  have cp : 0<c := by linarith only [cb.1]
  have Cp : 0<C := by linarith only [bb.1]
  have first := mul_nonneg (show 0≤A-9/10 by linarith only [An])
    (show 0≤s+S by linarith only [cn.1,bn.1])
  have last := mul_nonneg (show 0≤B+11/20 by linarith only [Bn])
    (show 0≤c+C by linarith only [cp,Cp])
  have bracket : 0≤A*(s+S)+B*(c+C) := by
    nlinarith only [first,last,steep,baseSteep,ca.1,ba.1]
  have product := mul_nonneg (sub_nonneg.mpr order) bracket
  have identity : (c+C)*((-A*c+B*s)-(-A*C+B*S))=
      (s-S)*(A*(s+S)+B*(c+C)) := by
    linear_combination -A*cn.2.2+A*bn.2.2
  have weighted : 0≤(c+C)*((-A*c+B*s)-(-A*C+B*S)) := by
    rw [identity]; exact product
  have result := nonneg_of_mul_nonneg_right weighted (show 0<c+C by linarith only [cp,Cp])
  linarith only [result]

private def lowerValue (d t : ℝ) : ℝ :=
  6/5-(4629/2500)*d+(4/5)*d^2-(108/125)*t+(3/5)*d*t

private theorem lower_endpoint {d t : ℝ} (en : Normal d t) (low : t≤3/5) :
    1/3125≤lowerValue d t := by
  have eb := normal_bounds en
  have dp : 0<d := by linarith only [eb.1]
  have dlow : 4/5≤d := CommonCases.UnitCircleChord.cosine_order dp.le
    (by norm_num) en.2.2 (by norm_num) en.1 (by norm_num) low
  let J := (t+3/5)*((4/5)*d-2129/2500)+
    (d+4/5)*(108/125-(3/5)*d)
  have first := mul_nonneg (show 0≤t+3/5 by linarith only [en.1])
    (show 0≤(4/5)*d-2129/2500+11/50 by linarith only [dlow])
  have last := mul_nonneg (show 0≤d+4/5 by linarith only [dp])
    (show 0≤108/125-(3/5)*d-33/125 by linarith only [eb.2.1])
  have bracket : 0≤J := by
    dsimp [J]
    nlinarith only [first,last,low,dlow]
  have product := mul_nonneg (show 0≤3/5-t by linarith only [low]) bracket
  have identity : (d+4/5)*(lowerValue d t-1/3125)=(3/5-t)*J := by
    dsimp [lowerValue,J]
    linear_combination ((4/5)*d-2129/2500)*en.2.2
  have weighted : 0≤(d+4/5)*(lowerValue d t-1/3125) := by
    rw [identity]; exact product
  have result := nonneg_of_mul_nonneg_right weighted (show 0<d+4/5 by linarith only [dp])
  linarith only [result]

theorem aligned_E {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) : 1/3125≤G00 c s d t d t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cp : 0<c := by linarith only [cb.1]
  have dp : 0<d := by linarith only [eb.1]
  by_cases order : t≤s
  · let A := d*(2-d)
    let B := 2-(1043/500)*d-(36/25)*t+d*t
    have coeff := coefficients en
    have dc : c*t-s*d≤0 := by
      have cross := CommonCases.UnitCircleChord.cross_order dp.le cp.le
        en.2.2 cn.2.2 en.1 cn.1 order
      nlinarith only [cross]
    have form : G00 c s d t d t=d-A*c+B*s := by
      dsimp [G00,k,kC,kE,deltaC,deltaE,C0,E0]
      rw [abs_of_nonpos dc,show d*t-t*d=0 by ring,abs_zero]
      dsimp [A,B]
      linear_combination s*en.2.2
    rw [form]
    by_cases qsteep : 3/5≤t
    · have comparison := move_up cn en steep qsteep order coeff.1 coeff.2
      have self : d-A*d+B*t=diagonalValue d t := by
        dsimp [A,B,diagonalValue]
        linear_combination (d-2)*en.2.2
      have base := diagonal_lower en qsteep
      linarith only [comparison,self,base]
    · have low : t≤3/5 := (lt_of_not_ge qsteep).le
      have normal0 : Normal (4/5) (3/5) := by norm_num [Normal]
      have comparison := move_up cn normal0 steep (by norm_num) steep coeff.1 coeff.2
      have self : d-A*(4/5)+B*(3/5)=lowerValue d t := by
        dsimp [A,B,lowerValue]
        ring
      have base := lower_endpoint en low
      linarith only [comparison,self,base]
  · have order : s≤t := (lt_of_not_ge order).le
    let A := d*(2-d-t)
    let B := 1-(1043/500)*d+t*(d+t-36/25)
    have small := canonical_bounds en
    have An : 0≤A := mul_nonneg dp.le
      (by linarith only [small.2.2.2.2])
    have product := mul_nonpos_of_nonneg_of_nonpos en.1
      (show d+t-36/25≤0 by linarith only [small.2.2.2.2])
    have Bn : 0≤-B := by dsimp [B]; nlinarith only [eb.1,product]
    have derivative : 0≤(-B)*d-A*t := by
      have bound : 0≤(1043/500)*d-(14/25)*t-1 := by
        linarith only [eb.1,en.2.1]
      have weight := mul_nonneg dp.le bound
      dsimp [A,B]
      nlinarith only [weight]
    have comparison := CommonCases.UnitCircleChord.increasing dp cp.le
      en.2.2 cn.2.2 en.1 cn.1 order An Bn derivative
    have dc : 0≤c*t-s*d := CommonCases.UnitCircleChord.cross_order cp.le dp.le
      cn.2.2 en.2.2 cn.1 en.1 order
    have form : G00 c s d t d t=d-A*c+B*s := by
      dsimp [G00,k,kC,kE,deltaC,deltaE,C0,E0]
      rw [abs_of_nonneg dc,show d*t-t*d=0 by ring,abs_zero]
      dsimp [A,B]
      ring
    have self : d-A*d+B*t=diagonalValue d t := by
      dsimp [A,B,diagonalValue]
      linear_combination (d+t-2)*en.2.2
    have base := diagonal_lower en (steep.trans order)
    rw [form]
    linarith only [comparison,self,base]

end
end N12Compact.C1092MPPMCrosspointSupport.Central
