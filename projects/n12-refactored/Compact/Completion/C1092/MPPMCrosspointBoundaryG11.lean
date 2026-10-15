import Compact.Completion.C1092.MPPMCrosspointBoundaryEnvelope
import Compact.Completion.C1092.MPPMCrosspointBoundaryEndpoints
import Compact.Completion.C1092.MPPMCrosspointBoundaryHalf

/-! The complete boundary-scalar G11 inequality. All estimates use the actual scalar inputs;
the upper FC coefficient .129 is a deliberately weaker rational cap. -/
namespace N12Compact.C1092MPPMCrosspointSupport
open C977CornerCubic C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

theorem G11_low_positive (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (q : Quarter h r)
    (hh : 4/5≤h) (rr : r≤3/5) : 0<G11 c s d t h r := by
  have cc := FC_low_cap c s h r cn steep q hh rr
  have ec := FE_low_cap d t h r en q hh rr
  have cweight := mul_le_mul_of_nonneg_left cc q.cosine
  have eweight := mul_le_mul_of_nonneg_left ec q.sine
  have lower := lower_endpoint_D h r q hh rr
  dsimp [G11]
  nlinarith only [cweight,eweight,lower,rr]

theorem G11_middle_positive (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (bn : Normal h r) (bs : 3/5≤r) :
    0<G11 c s d t h r := by
  have cc := FC_middle_cap c s h r cn steep bn bs
  have bb := normal_bounds bn
  have weighted := mul_le_mul_of_nonneg_left cc
    (show 0≤h by linarith only [bb.1])
  have positive := alignedBoundary_positive bn en bs
  dsimp [G11,alignedBoundary] at *
  nlinarith only [weighted,positive]

def G11High (d t h r : ℝ) : ℝ :=
  h+r-2+(457/1000)*h^2-(129/1000+P d t)*h*r+Q d t*r^2

theorem G11_high_bound (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (q : Quarter h r) (order : h≤r) :
    G11High d t h r≤G11 c s d t h r := by
  have first := mul_nonneg (sub_nonneg.mpr en.2.1) q.sine
  have last := mul_nonneg en.1 (sub_nonneg.mpr order)
  have branch : 0≤deltaE d t h r := by dsimp [deltaE]; nlinarith only [first,last]
  have cap := FC_high_cap c s h r cn steep q order
  have weighted := mul_le_mul_of_nonneg_left cap q.cosine
  have form := FE_after en branch
  dsimp [G11,G11High]
  rw [form]
  nlinarith only [weighted]

theorem G11High_vertical {d t : ℝ} (en : Normal d t) :
    0≤G11High d t 0 1 := by
  have bounds := coefficient_bounds en
  dsimp [G11High]
  nlinarith only [bounds.2.2.1]

theorem G11High_diagonal {d t v : ℝ} (en : Normal d t) (vn : Normal v v) :
    0<G11High d t v v := by
  have vb := normal_bounds vn
  have difference := coefficient_difference en
  have identity : G11High d t v v=2*v-459/250+(Q d t-P d t)/2 := by
    dsimp [G11High]
    linear_combination ((457/1000)-(129/1000+P d t)+Q d t)/2*vn.2.2
  nlinarith only [identity,difference,vb.1]

theorem G11High_form (d t h r : ℝ) (q : Quarter h r) :
    G11High d t h r=(Q d t-457/1000)*r^2-
      (129/1000+P d t)*r*h-1543/1000+h+r := by
  dsimp [G11High]
  linear_combination (457/1000)*q.unit

theorem G11_high_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (q : Quarter h r) (order : h≤r) :
    0≤G11 c s d t h r := by
  have rn : Normal r h := ⟨q.cosine,order,by nlinarith only [q.unit]⟩
  have hd := normal_half rn
  have rb := rho_bounds
  let z := half r h
  let a := Q d t-457/1000
  let b := -(129/1000+P d t)
  have coeff := coefficient_bounds en
  have an : 0≤a := by dsimp [a]; linarith only [coeff.2.2.1]
  have au : a≤731/1000 := by dsimp [a]; linarith only [coeff.2.2.2.1]
  have bl : -171/500≤b := by dsimp [b]; linarith only [coeff.2.1]
  have bu : b≤0 := by dsimp [b]; linarith only [coeff.1]
  have remainder := QuadraticArc.upper_remainder a b 0 z rho an au bl bu
    (by norm_num) (by norm_num) hd.1 (le_trans hd.2.1 rb.2.1.le) rb.1.le rb.2.1.le
  have first : 0≤QuadraticArc.value a b (-1543/1000) 1 1 0 := by
    have endpoint := G11High_vertical en
    simpa [QuadraticArc.value,G11High,cosH,sinH,a,b] using endpoint
  have diagonalNormal : Normal (Real.sqrt 2/2) (Real.sqrt 2/2) := by
    refine ⟨by positivity,le_rfl,?_⟩
    nlinarith only [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  have last : 0≤QuadraticArc.value a b (-1543/1000) 1 1 rho := by
    have endpoint := (G11High_diagonal en diagonalNormal).le
    have qp : Quarter (Real.sqrt 2/2) (Real.sqrt 2/2) :=
      ⟨by positivity,by positivity,diagonalNormal.2.2⟩
    rw [G11High_form _ _ _ _ qp] at endpoint
    dsimp [QuadraticArc.value,a,b]
    rw [rb.2.2.2.1,rb.2.2.2.2]
    nlinarith only [endpoint]
  have result := QuadraticArc.nonnegative a b (-1543/1000) 1 1 0 z rho
    (by norm_num) hd.1 hd.2.1 remainder first last
  have model : 0≤G11High d t h r := by
    rw [G11High_form d t h r q]
    dsimp [QuadraticArc.value] at result
    rw [hd.2.2.2.1,hd.2.2.2.2] at result
    dsimp [a,b] at result
    nlinarith only [result]
  exact le_trans model (G11_high_bound c s d t h r cn steep en q order)

theorem G11_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (q : Quarter h r) :
    0≤G11 c s d t h r := by
  by_cases low : r≤3/5
  · have cosine : 4/5≤h := by
      have first := mul_nonneg (show 0≤3/5-r by linarith only [low])
        (show 0≤3/5+r by linarith only [q.sine])
      apply le_of_not_gt
      intro bad
      have last := mul_pos (show 0<4/5-h by linarith only [bad])
        (show 0<4/5+h by linarith only [q.cosine])
      nlinarith only [first,last,q.unit]
    exact (G11_low_positive c s d t h r cn steep en q cosine low).le
  · by_cases high : h≤r
    · exact G11_high_nonnegative c s d t h r cn steep en q high
    · exact (G11_middle_positive c s d t h r cn steep en
        ⟨q.sine,(lt_of_not_ge high).le,q.unit⟩ (lt_of_not_ge low).le).le

end
end N12Compact.C1092MPPMCrosspointSupport
