import Compact.Completion.C1092.MPPMNegativeMissingPositiveCeilingScalars
import Compact.Completion.C1092.MPPMMissingPositiveBoundEnvelopesScalars
import Compact.Completion.C1092.MPPMCrosspointBoundaryHalf

/-! NEGATIVE-MISSING-POSITIVE-SHARED-WALL §§3--4. Full-arc scalar
proofs: rational quartic Bernstein bounds and finite circle differences
replace the manuscript derivatives. The coordinate endpoints are kept. -/
namespace N12Compact.C1092MPPMNegativeMissingPositiveSharedWall.Scalars
open C977CornerCubic C1092ShallowPositiveScalars C1092MPPMCrosspointSupport
open C1092MPPMMissingPositiveBoundaries.Envelopes
set_option Elab.async false
noncomputable section

def F0 (c s : ℝ) := 3/2-(6/5)*c-(36/25)*s+s*(c+s)/2
def A1 (c s : ℝ) := c+s-2+(14/25)*s^2-c*s
def B1 (c s : ℝ) := c-s-6/5+s^2+(14/25)*c*s
def A2 (c s : ℝ) := s-c-1-(11/25)*s^2
def B2 (c s : ℝ) := c+s-6/5-(11/25)*c*s

theorem bounds {c s : ℝ} (cn : Normal c s) (small : s/(1+c)≤3/10) :
    91/109≤c ∧ s≤60/109 := by
  have cb := normal_bounds cn
  have data := normal_half cn
  let x := half c s
  have xu : x≤3/10 := small
  have square := mul_nonneg (sub_nonneg.mpr xu)
    (show 0≤3/10+x by linarith only [data.1])
  have cp : 0<1+x^2 := by positivity
  have cform : (1+x^2)*c=1-x^2 := by
    have eq := (div_eq_iff cp.ne').mp data.2.2.2.1
    dsimp [cosH] at eq
    nlinarith only [eq]
  have cl : 91/109≤c := by
    have weighted : 0≤(1+x^2)*(c-91/109) := by nlinarith only [cform,square]
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right weighted cp)
  have product := mul_nonneg (sub_nonneg.mpr cl)
    (show 0≤c+91/109 by linarith only [cb.1])
  exact ⟨cl,by nlinarith only [product,cn.2.2,sq_nonneg (s-60/109)]⟩

theorem central_positive {c s : ℝ} (cn : Normal c s) (small : s/(1+c)≤3/10) :
    0<F0 c s := by
  let x := half c s
  have data := normal_half cn
  have xu : x≤3/10 := small
  have positive : 0<135*x^4-194*x^3+250*x^2-94*x+15 := by
    have first := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr xu)
    have last := sq_nonneg (x-235/959)
    have identity : 135*x^4-194*x^3+250*x^2-94*x+15=
        135*x^4+194*x^2*(3/10-x)+(959/5)*(x-235/959)^2+3340/959 := by ring
    nlinarith only [identity,first,last,pow_nonneg data.1 4]
  have identity : 50*(1+x^2)^2*F0 c s=135*x^4-194*x^3+250*x^2-94*x+15 := by
    rw [←data.2.2.2.1,←data.2.2.2.2]
    dsimp [F0,cosH,sinH]
    field_simp [(half_den_pos x).ne'] <;> ring
  have scaled : 0<50*(1+x^2)^2*F0 c s := by rw [identity]; exact positive
  exact pos_of_mul_pos_right scaled (by positivity)

theorem coefficients {c s : ℝ} (cn : Normal c s) (small : s/(1+c)≤3/10) :
    -1≤A1 c s ∧ -(9/25)≤B1 c s ∧ A2 c s≤-(7/5) ∧ -(1/5)≤B2 c s := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  let x := half c s
  have data := normal_half cn
  have xu : x≤3/10 := small
  have Dp : 0<1+x^2 := by positivity
  have aidentity : (1+c)*(A1 c s+1)=s^2*((14/25)*(1+c)-1+s) := by
    dsimp [A1]
    linear_combination (1-s)*cn.2.2
  have factor : 0≤(14/25)*(1+c)-1+s := by
    linarith only [cb.2.2.2.2.1,cp,cn.1]
  have apositive := mul_nonneg (sq_nonneg s) factor
  have al : -1≤A1 c s := by
    have weighted : 0≤(1+c)*(A1 c s+1) := by rw [aidentity]; exact apositive
    have result := nonneg_of_mul_nonneg_right weighted (show 0<1+c by linarith only [cp])
    linarith only [result]
  have bp := C1092MPPMNegativeCrosspointSupport.G01Quartic.bernstein
    4 (-22) 58 (-78) (-46) (3/10) x (by norm_num) data.1 xu
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [C1092MPPMNegativeCrosspointSupport.G01Quartic.poly])
  have bidentity : 25*(1+x^2)^2*(B1 c s+9/25)=
      C1092MPPMNegativeCrosspointSupport.G01Quartic.poly 4 (-22) 58 (-78) (-46) x := by
    rw [←data.2.2.2.1,←data.2.2.2.2]
    dsimp [B1,cosH,sinH,C1092MPPMNegativeCrosspointSupport.G01Quartic.poly]
    field_simp [Dp.ne'] <;> ring
  have bl : -(9/25)≤B1 c s := by
    have weighted : 0≤25*(1+x^2)^2*(B1 c s+9/25) := by rw [bidentity]; exact bp
    have result := nonneg_of_mul_nonneg_right weighted (by positivity : 0<25*(1+x^2)^2)
    linarith only [result]
  have ap := C1092MPPMNegativeCrosspointSupport.G01Quartic.bernstein
    15 (-50) 24 (-50) (-35) (3/10) x (by norm_num) data.1 xu
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [C1092MPPMNegativeCrosspointSupport.G01Quartic.poly])
  have second : 25*(1+x^2)^2*(-A2 c s-7/5)=
      C1092MPPMNegativeCrosspointSupport.G01Quartic.poly 15 (-50) 24 (-50) (-35) x := by
    rw [←data.2.2.2.1,←data.2.2.2.2]
    dsimp [A2,cosH,sinH,C1092MPPMNegativeCrosspointSupport.G01Quartic.poly]
    field_simp [Dp.ne'] <;> ring
  have ah : A2 c s≤-(7/5) := by
    have weighted : 0≤25*(1+x^2)^2*(-A2 c s-7/5) := by rw [second]; exact ap
    have result := nonneg_of_mul_nonneg_right weighted (by positivity : 0<25*(1+x^2)^2)
    linarith only [result]
  have bfactor := mul_nonneg (mul_nonneg cp.le cn.1)
    (show 0≤2-(11/25)*(1+c+s) by linarith only [cb.2.2.2.2.2])
  have last : (1+c+s)*(B2 c s+1/5)=c*s*(2-(11/25)*(1+c+s)) := by
    dsimp [B2]
    linear_combination cn.2.2
  have bll : -(1/5)≤B2 c s := by
    have weighted : 0≤(1+c+s)*(B2 c s+1/5) := by rw [last]; exact bfactor
    have result := nonneg_of_mul_nonneg_right weighted (by linarith only [cp,cn.1])
    linarith only [result]
  exact ⟨al,bl,ah,bll⟩

theorem model_nonnegative {h r : ℝ} (q : Quarter h r) :
    0≤(1-h)^2/2+r*(h/2-9/25) := by
  let z := half h r
  have data := quarter_half q
  have cubic : 0≤z^3-(43/50)*z^2+7/50 := by
    have product := mul_nonneg (sq_nonneg (z-43/75))
      (show 0≤z+43/150 by linarith only [data.1])
    have identity : z^3-(43/50)*z^2+7/50=
        (z-43/75)^2*(z+43/150)+19309/421875 := by ring
    nlinarith only [product,identity]
  have identity : (1-h)^2/2+r*(h/2-9/25)=
      2*z*(z^3-(43/50)*z^2+7/50)/(1+z^2)^2 := by
    rw [←data.2.2.1,←data.2.2.2]
    dsimp [cosH,sinH]
    field_simp [(half_den_pos z).ne'] <;> ring
  rw [identity]
  exact div_nonneg (mul_nonneg (by linarith only [data.1]) cubic) (sq_nonneg _)

theorem northwest_before {c s h r : ℝ} (cn : Normal c s) (small : s/(1+c)≤3/10)
    (q : Quarter h r) : 0≤leftValue 1 (A1 c s) (B1 c s) h r := by
  have bounds := coefficients cn small
  have first := mul_nonneg (show 0≤A1 c s+1 by linarith only [bounds.1]) q.cosine
  have second := mul_nonneg (show 0≤B1 c s+9/25 by linarith only [bounds.2.1]) q.sine
  have model := model_nonnegative q
  dsimp [leftValue]
  nlinarith only [first,second,model]

theorem northwest_after {c s h r : ℝ} (cn : Normal c s) (positive : 0<s)
    (small : s/(1+c)≤3/10) (q : Quarter h r) (order : 0≤s*r-c*h) :
    0<leftValue 1 (A2 c s) (B2 c s) h r := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have interval := bounds cn small
  have coefficients := coefficients cn small
  have range := circle_order c s h r cp positive q.cosine q.sine cn.2.2 q.unit order
  let H := (h+s)/2
  let T := (r+c)/2
  have Hp : 0<H := by dsimp [H]; linarith only [q.cosine,positive]
  have Hh : H≤5/9 := by dsimp [H]; linarith only [range.1,interval.2]
  have Tl : 5/6≤T := by dsimp [T]; linarith only [range.2,interval.1]
  have Th : T≤1 := by
    have rh : r≤1 := by nlinarith only [q.unit,sq_nonneg h,sq_nonneg (r-1)]
    dsimp [T]; linarith only [rh,cb.2.1]
  have first := mul_nonneg (show 0≤-A2 c s-7/5 by linarith only [coefficients.2.2.1])
    (show 0≤T by linarith only [Tl])
  have second := mul_nonneg (show 0≤B2 c s+1/5 by linarith only [coefficients.2.2.2]) Hp.le
  have reserve := mul_nonneg (show 0≤T by linarith only [Tl])
    (show 0≤7/5-H-T/2-31/90 by linarith only [Hh,Th])
  have endpoint := mul_nonneg (sub_nonneg.mpr Tl) (by norm_num : (0:ℝ)≤31/90)
  have derivative : 0≤-H*T+(H^2-T^2)/2-A2 c s*T+B2 c s*H := by
    nlinarith only [first,second,reserve,endpoint,sq_nonneg H,Hh]
  have product := mul_nonneg (sub_nonneg.mpr range.2) derivative
  have identity := left_difference 1 (A2 c s) (B2 c s) h r s c
    (by nlinarith only [q.unit,cn.2.2])
  have difference : 0≤H*(leftValue 1 (A2 c s) (B2 c s) h r-
      leftValue 1 (A2 c s) (B2 c s) s c) := by
    change 0≤((h+s)/2)*_
    rw [identity]
    exact product
  have monotone := nonneg_of_mul_nonneg_right difference Hp
  have aligned : leftValue 1 (A2 c s) (B2 c s) s c=F0 c s := by
    dsimp [leftValue,A2,B2,F0]
    linear_combination (1-(11/25)*s)*cn.2.2
  rw [aligned] at monotone
  have central := central_positive cn small
  linarith only [monotone,central]

end
end N12Compact.C1092MPPMNegativeMissingPositiveSharedWall.Scalars
