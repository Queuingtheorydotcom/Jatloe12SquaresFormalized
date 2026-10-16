import Compact.Completion.C1092.MPPMCrosspointBoundaryCoefficients
import Compact.Completion.C1092.MPPMCrosspointBoundaryG10Clamp
import Compact.Completion.C1092.MPPMNonpositivePredecessorScalars
import Compact.Completion.C1092.WallProfileScalars
import Compact.Completion.CommonCases.UnitCircleChord

/-! BOUNDARY-SCALARS section 4.2. The rational half-angle interval
[0,5/12] contains the required interval [0,sqrt(2)-1]. Its extended
endpoint has the rational normal (120/169,119/169), and a direct Cauchy
bound still gives a strict margin. Thus the five Bernstein coefficients
can be proved without algebraic endpoints or angular differentiation. -/
namespace N12Compact.C1092MPPMCrosspointSupport
open C977CornerCubic
set_option Elab.async false
noncomputable section

private def highQuartic (c s A B z : ℝ) : ℝ :=
  (s-B)+2*(c+s-A)*z+(4*c-2*s)*z^2-
    2*(c+s+A)*z^3+(s+B)*z^4

private theorem coefficients (c s d t : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) :
    let A := 2*c+(543/500)*s-1+s*P d t
    let B := s*(2-Q d t)
    A≤c+s ∧ B≤s ∧ A+B≤2*c+(549/250)*s-1 := by
  dsimp only
  have cb := normal_bounds cn
  have eb := coefficient_bounds en
  have fixed : Normal (4/5:ℝ) (3/5) := by norm_num [Normal]
  have chord := CommonCases.UnitCircleChord.decreasing (A := (3:ℝ)) (B := 1)
    (show (0:ℝ)<4/5 by norm_num) (show 0≤c by linarith only [cb.1])
    fixed.2.2 cn.2.2 fixed.1 cn.1 steep (by norm_num) (by norm_num) (by norm_num)
  have pWeight := mul_le_mul_of_nonneg_left eb.2.1.le cn.1
  have qWeight := mul_le_mul_of_nonneg_left eb.2.2.2.2.2.1 cn.1
  have sumWeight := mul_le_mul_of_nonneg_left eb.2.2.2.2.2.2.le cn.1
  refine ⟨?_,by simpa only [mul_one] using qWeight,?_⟩ <;>
    nlinarith only [chord,pWeight,sumWeight,cn.1]

private theorem quartic_nonnegative (c s A B z : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (Acap : A≤c+s) (Bcap : B≤s)
    (sumcap : A+B≤2*c+(549/250)*s-1) (zn : 0≤z) (zu : z≤5/12) :
    0≤highQuartic c s A B z := by
  have cb := normal_bounds cn
  have sb := steep_bounds cn steep
  let R : ℝ := 5/12
  let b0 := s-B
  let b1 := b0+(c+s-A)*R/2
  let b2 := b0+(c+s-A)*R+(4*c-2*s)*R^2/6
  let b3 := b0+(3/2)*(c+s-A)*R+(2*c-s)*R^2-(c+s+A)*R^3/2
  let b4 := highQuartic c s A B R
  have gap : 0≤c+s-A := by linarith only [Acap]
  have b0n : 0≤b0 := by dsimp [b0]; linarith only [Bcap]
  have b1n : 0≤b1 := by dsimp [b1,R]; linarith only [b0n,gap]
  have b2n : 0≤b2 := by
    dsimp [b2,R]
    nlinarith only [b0n,gap,cn.2.1,cb.1]
  have low : 7/10≤2*c-s := by linarith only [cn.2.1,cb.1]
  have high : c+s+A≤283/100 := by linarith only [Acap,sb.2.2.2]
  have b3n : 0≤b3 := by
    dsimp [b3,R]
    nlinarith only [b0n,gap,low,high]
  have endpoint : 0<(c-s)*(120/169)^2+(c+s)*(120/169)*(119/169)+s-
      A*(120/169)-B*(119/169) := by
    have sumWeight := mul_le_mul_of_nonneg_right sumcap (show (0:ℝ)≤119/169 by norm_num)
    have extraWeight := mul_le_mul_of_nonneg_right Acap (show (0:ℝ)≤1/169 by norm_num)
    have comparison : 119/169-(411/1000)*c-(557/1000)*s≤
        (c-s)*(120/169)^2+(c+s)*(120/169)*(119/169)+s-
          A*(120/169)-B*(119/169) := by
      nlinarith only [sumWeight,extraWeight,cb.1,cn.1]
    have norm := C1092MPPMNonpositivePredecessor.norm_lt (411/1000) (557/1000) c s (7/10)
      cn.2.2 (by norm_num) (by norm_num)
    linarith only [comparison,norm]
  have endpointIdentity : b4=(1+(5/12:ℝ)^2)^2*
      ((c-s)*(120/169)^2+(c+s)*(120/169)*(119/169)+s-
        A*(120/169)-B*(119/169)) := by
    dsimp [b4,R,highQuartic]
    ring
  have b4n : 0≤b4 := by rw [endpointIdentity]; positivity
  have rest : 0≤R-z := by dsimp [R]; linarith only [zu]
  have first := mul_nonneg b0n (pow_nonneg rest 4)
  have second := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) b1n) zn)
    (pow_nonneg rest 3)
  have third := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤6) b2n) (sq_nonneg z))
    (sq_nonneg (R-z))
  have fourth := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) b3n) (pow_nonneg zn 3)) rest
  have fifth := mul_nonneg b4n (pow_nonneg zn 4)
  have identity : R^4*highQuartic c s A B z=
      b0*(R-z)^4+4*b1*z*(R-z)^3+6*b2*z^2*(R-z)^2+
        4*b3*z^3*(R-z)+b4*z^4 := by
    dsimp [b0,b1,b2,b3,b4,highQuartic]
    ring
  have weighted : 0≤R^4*highQuartic c s A B z := by
    rw [identity]
    linarith only [first,second,third,fourth,fifth]
  exact nonneg_of_mul_nonneg_right weighted (by dsimp [R]; norm_num)

theorem G01_high_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (q : Quarter h r)
    (order : h≤r) : 0≤G01 c s d t h r := by
  have cfirst := mul_nonneg (sub_nonneg.mpr cn.2.1) q.sine
  have clast := mul_nonneg cn.1 (sub_nonneg.mpr order)
  have corder : 0≤deltaC c s h r := by dsimp [deltaC]; nlinarith only [cfirst,clast]
  have efirst := mul_nonneg (sub_nonneg.mpr en.2.1) q.sine
  have elast := mul_nonneg en.1 (sub_nonneg.mpr order)
  have eorder : 0≤deltaE d t h r := by dsimp [deltaE]; nlinarith only [efirst,elast]
  let A := 2*c+(543/500)*s-1+s*P d t
  let B := s*(2-Q d t)
  have bounds := coefficients c s d t cn steep en
  change A≤c+s ∧ B≤s ∧ A+B≤2*c+(549/250)*s-1 at bounds
  have formula : G01 c s d t h r=(c-s)*h^2+(c+s)*h*r+s-A*h-B*r := by
    unfold G01
    rw [abs_of_nonneg corder,FE_after en eorder]
    dsimp [kC,deltaC,C0,A,B]
    linear_combination (s/2)*q.unit
  let z := C1092WallProfileScalars.half r h
  have data := C1092WallProfileScalars.quarter_data r h q.sine q.cosine
    (by nlinarith only [q.unit])
  have zn : 0≤z := data.1
  have denominator : 0<1+z^2 := by positivity
  have rdata : (1+z^2)*r=1-z^2 := data.2.2.2.1
  have hdata : (1+z^2)*h=2*z := data.2.2.2.2
  have orderWeight := mul_le_mul_of_nonneg_left order denominator.le
  have quadratic : z^2+2*z≤1 := by nlinarith only [rdata,hdata,orderWeight]
  have zu : z≤5/12 := by
    apply le_of_not_gt
    intro no
    have square := mul_pos (show 0<z-5/12 by linarith only [no])
      (show 0<z+5/12+2 by linarith only [zn])
    nlinarith only [square,quadratic]
  have hform : h=2*z/(1+z^2) := by
    apply (eq_div_iff denominator.ne').mpr
    nlinarith only [hdata]
  have rform : r=(1-z^2)/(1+z^2) := by
    apply (eq_div_iff denominator.ne').mpr
    nlinarith only [rdata]
  have identity : highQuartic c s A B z=(1+z^2)^2*G01 c s d t h r := by
    rw [formula,hform,rform]
    dsimp [highQuartic]
    field_simp [denominator.ne'] <;> ring
  have poly := quartic_nonnegative c s A B z cn steep bounds.1 bounds.2.1 bounds.2.2 zn zu
  rw [identity] at poly
  exact nonneg_of_mul_nonneg_right poly (sq_pos_of_pos denominator)

#print axioms G01_high_nonnegative
end
end N12Compact.C1092MPPMCrosspointSupport
