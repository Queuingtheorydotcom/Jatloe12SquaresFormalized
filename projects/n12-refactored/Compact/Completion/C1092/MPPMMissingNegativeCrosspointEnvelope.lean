import Compact.Completion.C1092.MPPMMissingNegativeCrosspointCentral
import Compact.Completion.C1092.MPPMNegativeCrosspointClamp

/-! MISSING-NEGATIVE-WALL-SCALARS section 2, simplified. The literal
FE is the minimum of two linear branches; both envelope bounds therefore
hold on the whole quadrant. The delicate coefficient is bounded by the
quadratic .35+.295(d-t)+.15(d-t)^2 using d+t>=1.41. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointSupport
open C977CornerCubic
set_option Elab.async false
noncomputable section

private def leftSupport (d t h r : ℝ) : ℝ :=
  -deltaE d t h r*(d+t-1)+kE d t h r*E0 d t
private def rightSupport (d t h r : ℝ) : ℝ :=
  -deltaE d t h r*(1+(13/50)*t)+kE d t h r*E0 d t

theorem FE_both_caps (d t h r : ℝ) (en : Normal d t) :
    FE d t h r≤leftSupport d t h r ∧ FE d t h r≤rightSupport d t h r := by
  have eb := normal_bounds en
  have coefficient : 0≤2-d-(37/50)*t := by linarith only [eb.2.1,eb.2.2.2.1]
  by_cases branch : 0≤deltaE d t h r
  · have product := mul_nonneg branch coefficient
    rw [FE,if_pos branch]
    dsimp [leftSupport,rightSupport]
    constructor <;> nlinarith only [product]
  · have product := mul_nonpos_of_nonpos_of_nonneg (lt_of_not_ge branch).le coefficient
    rw [FE,if_neg branch]
    dsimp [leftSupport,rightSupport]
    constructor <;> nlinarith only [product]

theorem large_sum {d t : ℝ} (en : Normal d t) (large : 252/373≤t) : 141/100≤d+t := by
  have eb := normal_bounds en
  have endpoint : Normal (275/373:ℝ) (252/373) := by norm_num [Normal]
  have order := CommonCases.UnitCircleChord.increasing (A:=(1:ℝ)) (B:=1)
    (show 0<d by linarith only [eb.1]) (by norm_num : (0:ℝ)≤275/373)
    en.2.2 endpoint.2.2 en.1 endpoint.1 large (by norm_num) (by norm_num)
    (by linarith only [en.2.1])
  linarith only [order]

theorem FE_first_cap (d t h r : ℝ) (en : Normal d t) (large : 252/373≤t)
    (q : Quarter h r) : FE d t h r≤-(19/100)*h-(39/50)*r := by
  have eb := normal_bounds en
  have sum := large_sum en large
  have dt : d*t≤1/2 := by nlinarith only [en.2.2,sq_nonneg (d-t)]
  have A : 1-d-t+(11/25)*d*t≤-19/100 := by linarith only [sum,dt]
  have product := mul_nonneg (sub_nonneg.mpr en.2.1)
    (show 0≤1-(11/50)*(d+t) by linarith only [eb.2.2.2.2.2])
  have B : t-d-14/25-(11/25)*t^2≤-39/50 := by nlinarith only [product,en.2.2]
  have aw := mul_le_mul_of_nonneg_right A q.cosine
  have bw := mul_le_mul_of_nonneg_right B q.sine
  have formula : leftSupport d t h r=
      (1-d-t+(11/25)*d*t)*h+(t-d-14/25-(11/25)*t^2)*r := by
    dsimp [leftSupport,deltaE,kE,E0]
    linear_combination (h-(14/25)*r)*en.2.2
  have cap := (FE_both_caps d t h r en).1
  rw [formula] at cap
  nlinarith only [aw,bw,cap]

theorem FE_second_cap (d t h r : ℝ) (en : Normal d t) (large : 252/373≤t)
    (q : Quarter h r) : FE d t h r≤(37/100)*h-(33/25)*r := by
  have eb := normal_bounds en
  have endpoint : Normal (275/373:ℝ) (252/373) := by norm_num [Normal]
  have cosine := C977CornerSectorBounds.cosine_order en endpoint large
  have difference : d-t≤23/373 := by linarith only [cosine,large]
  have chord := mul_nonneg (show 0≤23/373-(d-t) by linarith only [difference])
    (show 0≤59/200+(3/20)*(23/373+d-t) by linarith only [en.2.1])
  have sum := large_sum en large
  have sumProduct := mul_nonneg (sub_nonneg.mpr en.2.1)
    (show 0≤d+t-141/100 by linarith only [sum])
  have A : d-t+t^2-(3/10)*d*t≤37/100 := by
    nlinarith only [chord,sumProduct,en.2.2]
  have order := mul_nonneg (sub_nonneg.mpr en.2.1)
    (show 0≤d+t by linarith only [eb.1,en.1])
  have tcap : t^2≤1/2 := by nlinarith only [order,en.2.2]
  have dt : d*t≤1/2 := by nlinarith only [en.2.2,sq_nonneg (d-t)]
  have B : -d-t-14/25+(3/10)*t^2+d*t≤-33/25 := by
    linarith only [large_sum en large,tcap,dt]
  have aw := mul_le_mul_of_nonneg_right A q.cosine
  have bw := mul_le_mul_of_nonneg_right B q.sine
  have formula : rightSupport d t h r=
      (d-t+t^2-(3/10)*d*t)*h+(-d-t-14/25+(3/10)*t^2+d*t)*r := by
    dsimp [rightSupport,deltaE,kE,E0]
    linear_combination (-(14/25)*r)*en.2.2
  have cap := (FE_both_caps d t h r en).2
  rw [formula] at cap
  nlinarith only [aw,bw,cap]

end
#print axioms FE_first_cap
#print axioms FE_second_cap
end N12Compact.C1092MPPMMissingNegativeCrosspointSupport
