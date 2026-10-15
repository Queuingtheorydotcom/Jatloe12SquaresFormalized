import Compact.Completion.C1092.MPPMMissingNegativeCrosspointEnvelope
import Compact.Completion.C1092.MPPMMissingNegativeCrosspointG11Remainders

/-! Full MISSING-NEGATIVE-WALL-SCALARS G11*, with a uniform rational
positive margin. Both FE envelopes hold globally, so only the three real
C-clamp pieces remain. Exact quadratic circle interpolation replaces all
four concavity arguments, including every joining and coordinate endpoint. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointSupport
open C977CornerCubic C1092ShallowPositiveScalars C1092MPPMCrosspointSupport
set_option Elab.async false
noncomputable section

private theorem perturbation {epsilon c s h r : ℝ} (cn : Normal c s)
    (q : Quarter h r) (allowance : epsilon≤43/500) :
    epsilon*s*h*kC c s h r≤(9/200)*h*(h+r) := by
  have cb := normal_bounds cn
  have cp : 0≤c := by linarith only [cb.1]
  have cs : c*s≤1/2 := by nlinarith only [cn.2.2,sq_nonneg (c-s)]
  have order := mul_nonneg (sub_nonneg.mpr cn.2.1) (add_nonneg cp cn.1)
  have ss : s^2≤1/2 := by nlinarith only [order,cn.2.2]
  have first := mul_le_mul_of_nonneg_right cs q.cosine
  have last := mul_le_mul_of_nonneg_right ss q.sine
  have kn : 0≤kC c s h r := add_nonneg (mul_nonneg cp q.cosine) (mul_nonneg cn.1 q.sine)
  have weight := mul_le_mul_of_nonneg_right allowance
    (mul_nonneg (mul_nonneg cn.1 q.cosine) kn)
  have cap := mul_nonneg q.cosine
    (show 0≤(h+r)/2-s*kC c s h r by dsimp [kC]; nlinarith only [first,last])
  have extra := mul_nonneg q.cosine (add_nonneg q.cosine q.sine)
  nlinarith only [weight,cap,extra]

private def lowModel (h r : ℝ) : ℝ := h+r-177/200-(67/200)*r^2-(147/200)*h*r
private def middleModel (h r : ℝ) : ℝ := 2*h+r-409/200-(171/200)*h*r+(33/40)*r^2
private def highModel (h r : ℝ) : ℝ := h+r-309/200+(173/200)*r^2-(101/200)*h*r

private theorem low_model_positive (h r : ℝ) (q : Quarter h r)
    (hh : 4/5≤h) (rr : r≤3/5) : 1/100≤lowModel h r := by
  have bn : Normal h r := ⟨q.sine,by linarith only [hh,rr],q.unit⟩
  have hd := normal_half bn
  have base : Normal (4/5:ℝ) (3/5) := by norm_num [Normal]
  have order := half_order bn base rr
  have zu : half h r≤1/3 := by norm_num [half] at order; exact order
  have rem := low_remainder (half h r) hd.1 zu
  have result := QuadraticArc.nonnegative (67/200) (-(147/200)) (-(123/100)) 1 1
    0 (half h r) (1/3) (by norm_num) hd.1 zu rem
    (by norm_num [QuadraticArc.value,cosH,sinH])
    (by norm_num [QuadraticArc.value,cosH,sinH])
  dsimp [QuadraticArc.value] at result
  rw [hd.2.2.2.1,hd.2.2.2.2] at result
  dsimp [lowModel]
  nlinarith only [result,q.unit]

private theorem middle_model_positive (h r : ℝ) (bn : Normal h r)
    (steep : 3/5≤r) : 1/100≤middleModel h r := by
  have hd := normal_half bn
  have rb := rho_bounds
  have lower := steep_half bn steep
  have lowerRho : (1/3:ℝ)≤rho := by
    apply le_of_not_gt
    intro bad
    have product := mul_nonneg rb.1.le (show 0≤1/3-rho by linarith only [bad])
    nlinarith only [product,rb.2.2.1,bad]
  have rem := middle_remainder (1/3) (half h r) rho
    (by norm_num) (by norm_num) lower (le_trans hd.2.1 rb.2.1.le)
    lowerRho rb.2.1.le
  have vn : Normal (Real.sqrt 2/2) (Real.sqrt 2/2) := by
    refine ⟨by positivity,le_rfl,?_⟩
    nlinarith only [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  have endpoint : 0≤QuadraticArc.value (-(33/40)) (-(171/200)) (-(123/100)) 2 1 rho := by
    dsimp [QuadraticArc.value]
    rw [rb.2.2.2.1,rb.2.2.2.2]
    nlinarith only [vn.2.2,(normal_bounds vn).1]
  have result := QuadraticArc.nonnegative (-(33/40)) (-(171/200)) (-(123/100)) 2 1
    (1/3) (half h r) rho (by norm_num) lower hd.2.1 rem
    (by norm_num [QuadraticArc.value,cosH,sinH]) endpoint
  dsimp [QuadraticArc.value] at result
  rw [hd.2.2.2.1,hd.2.2.2.2] at result
  dsimp [middleModel]
  nlinarith only [result,bn.2.2]

private theorem high_model_positive (h r : ℝ) (q : Quarter h r)
    (order : h≤r) : 1/100≤highModel h r := by
  have bn : Normal r h := ⟨q.cosine,order,by nlinarith only [q.unit]⟩
  have hd := normal_half bn
  have rb := rho_bounds
  have rem := high_remainder (half r h) rho hd.1 (le_trans hd.2.1 rb.2.1.le)
    rb.1.le rb.2.1.le
  have vn : Normal (Real.sqrt 2/2) (Real.sqrt 2/2) := by
    refine ⟨by positivity,le_rfl,?_⟩
    nlinarith only [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  have endpoint : 0≤QuadraticArc.value (173/200) (-(101/200)) (-(311/200)) 1 1 rho := by
    dsimp [QuadraticArc.value]
    rw [rb.2.2.2.1,rb.2.2.2.2]
    nlinarith only [vn.2.2,(normal_bounds vn).1]
  have result := QuadraticArc.nonnegative (173/200) (-(101/200)) (-(311/200)) 1 1
    0 (half r h) rho (by norm_num) hd.1 hd.2.1 rem
    (by norm_num [QuadraticArc.value,cosH,sinH]) endpoint
  dsimp [QuadraticArc.value] at result
  rw [hd.2.2.2.1,hd.2.2.2.2] at result
  dsimp [highModel]
  nlinarith only [result]

/-- Shared middle-arc scalar, also used by the literal G01 clamp. -/
theorem middle_scalar_lower (h r : ℝ) (bn : Normal h r) (steep : 3/5≤r) :
    1/100≤2*h+r-409/200-(171/200)*h*r+(33/40)*r^2 :=
  middle_model_positive h r bn steep

theorem G11star_lower (epsilon c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (large : 252/373≤t)
    (q : Quarter h r) (allowance : epsilon≤43/500) :
    1/100≤G11star epsilon c s d t h r := by
  have perturb := perturbation cn q allowance
  have first := FE_first_cap d t h r en large q
  have second := FE_second_cap d t h r en large q
  by_cases low : r≤3/5
  · have hh : 4/5≤h := by
      have first := mul_nonneg (show 0≤3/5-r by linarith only [low])
        (show 0≤3/5+r by linarith only [q.sine])
      apply le_of_not_gt
      intro bad
      have last := mul_pos (show 0<4/5-h by linarith only [bad])
        (show 0<4/5+h by linarith only [q.cosine])
      nlinarith only [first,last,q.unit]
    have cap := C1092MPPMNegativeCrosspointSupport.FC_low_cap c s h r cn steep q hh low
    have cw := mul_le_mul_of_nonneg_left cap q.cosine
    have ew := mul_le_mul_of_nonneg_left first q.sine
    have model := low_model_positive h r q hh low
    dsimp [G11star,G11,lowModel] at *
    nlinarith only [cw,ew,perturb,model,q.unit]
  · by_cases high : h≤r
    · have cap := C1092MPPMNegativeCrosspointSupport.FC_high_cap c s h r cn q high
      have cw := mul_le_mul_of_nonneg_left cap q.cosine
      have ew := mul_le_mul_of_nonneg_left second q.sine
      have model := high_model_positive h r q high
      dsimp [G11star,G11,highModel] at *
      nlinarith only [cw,ew,perturb,model,q.unit]
    · have bn : Normal h r := ⟨q.sine,(lt_of_not_ge high).le,q.unit⟩
      have cap := C1092MPPMNegativeCrosspointSupport.FC_middle_cap c s h r cn steep bn
        (lt_of_not_ge low).le
      have cw := mul_le_mul_of_nonneg_left cap q.cosine
      have ew := mul_le_mul_of_nonneg_left first q.sine
      have model := middle_model_positive h r bn (lt_of_not_ge low).le
      dsimp [G11star,G11,middleModel] at *
      nlinarith only [cw,ew,perturb,model,q.unit]

end
#print axioms G11star_lower
end N12Compact.C1092MPPMMissingNegativeCrosspointSupport
