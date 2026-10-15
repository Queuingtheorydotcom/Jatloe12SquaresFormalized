import Compact.Completion.C1092.MPPMNegativeCrosspointCentral
import Compact.Completion.C1092.MPPMSteepPositiveNegativeProfileScalars

/-! The unperturbed C support clamps in NEGATIVE-WALL-SCALARS section 3.
Exact circle products replace angular differentiation. The upper clamp is
weakened to the rational .09; this retains a strict reserve in G10. -/
namespace N12Compact.C1092MPPMNegativeCrosspointSupport
open C977CornerCubic
set_option Elab.async false
noncomputable section

theorem FC_lower_formula {c s h r : ℝ} (order : deltaC c s h r≤0) :
    FC c s h r=(-c-s+c*s/2)*h+(c-s+c^2/2+s^2)*r := by
  by_cases branch : 0≤deltaC c s h r
  · have zero : deltaC c s h r=0 := le_antisymm order branch
    rw [FC,if_pos branch]
    dsimp [deltaC,kC] at zero ⊢
    linear_combination (c/2+s-2)*zero
  · rw [FC,if_neg branch]
    dsimp [deltaC,kC]
    ring

theorem FC_upper_formula {c s h r : ℝ} (cn : Normal c s)
    (order : 0≤deltaC c s h r) :
    FC c s h r=(-c+s-s^2)*h+(1+c*s-c-s)*r := by
  rw [FC,if_pos order]
  dsimp [deltaC,kC]
  linear_combination r*cn.2.2

theorem FC_low_cap (c s h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (q : Quarter h r) (hh : 4/5≤h) (rr : r≤3/5) :
    FC c s h r≤-(29/25)*h+(22/25)*r := by
  have cb := normal_bounds cn
  have sb := C1092MPPMCrosspointSupport.steep_bounds cn steep
  have first := mul_nonneg (show 0≤c by linarith only [cb.1])
    (show 0≤3/5-r by linarith only [rr])
  have last := mul_nonneg cn.1 (show 0≤h-4/5 by linarith only [hh])
  have order : deltaC c s h r≤0 := by
    dsimp [deltaC]
    nlinarith only [first,last,sb.1,steep]
  have sum := mul_nonneg (show 0≤c+s-7/5 by linarith only [sb.2.2.1])
    (show 0≤1-(c+s+7/5)/4 by linarith only [sb.2.2.2])
  have sine := mul_nonneg (sub_nonneg.mpr steep)
    (show 0≤1-(s+3/5)/2 by linarith only [sb.2.1])
  have A : -c-s+c*s/2≤-29/25 := by nlinarith only [sum,cn.2.2]
  have B : c-s+c^2/2+s^2≤22/25 := by nlinarith only [sine,sb.1,cn.2.2]
  have weightA := mul_le_mul_of_nonneg_right A q.cosine
  have weightB := mul_le_mul_of_nonneg_right B q.sine
  rw [FC_lower_formula order]
  linarith only [weightA,weightB]

theorem FC_middle_cap (c s h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (bn : Normal h r) (bs : 3/5≤r) : FC c s h r≤r-1 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cs := C1092MPPMCrosspointSupport.steep_bounds cn steep
  have bs' := C1092MPPMCrosspointSupport.steep_bounds bn bs
  let a := kC c s h r
  let z := deltaC c s h r
  have ap : 0<a := by
    have first := mul_pos (show 0<c by linarith only [cb.1])
      (show 0<h by linarith only [bb.1])
    have last := mul_nonneg cn.1 bn.1
    dsimp [a,kC]
    nlinarith only [first,last]
  have ah : a≤1 := by dsimp [a,kC]; exact C977CornerSectorBounds.dot_le_one cn bn
  have unit : a^2+z^2=1 := by
    dsimp [a,z,kC,deltaC]
    linear_combination (h^2+r^2)*cn.2.2+bn.2.2
  have rIdentity : r=a*s+z*c := by
    dsimp [a,z,kC,deltaC]
    linear_combination -r*cn.2.2
  have chord := mul_nonneg ap.le (show 0≤1-a by linarith only [ah])
  by_cases order : 0≤z
  · have first := mul_nonneg cn.1 (sub_nonneg.mpr bn.2.1)
    have last := mul_nonneg bn.1 (show 0≤1/5-(c-s) by linarith only [cs.1,steep])
    have small : z<3/20 := by dsimp [z,deltaC]; nlinarith only [first,last,bs'.2.1]
    have square := mul_nonneg order (show 0≤3/20-z by linarith only [small])
    have gap : 1-a≤(3/20)*z := by nlinarith only [unit,chord,square]
    have coefficient := mul_nonneg order (show 0≤17/20-s by linarith only [cs.2.1])
    have formula : FC c s h r-(r-1)=1-a+z*(s-1) := by
      rw [FC,if_pos order]
      change z*(c+s)+a*s-(a+z)-(r-1)=_
      nlinarith only [rIdentity]
    nlinarith only [formula,gap,coefficient]
  · have nonpositive : z≤0 := (lt_of_not_ge order).le
    have first := mul_nonneg bn.1 (sub_nonneg.mpr cn.2.1)
    have last := mul_nonneg cn.1 (show 0≤1/5-(h-r) by linarith only [bs'.1,bs])
    have small : -z<3/20 := by dsimp [z,deltaC]; nlinarith only [first,last,cs.2.1]
    have square := mul_nonneg (neg_nonneg.mpr nonpositive)
      (show 0≤3/20+z by linarith only [small])
    have gap : 1-a≤-(3/20)*z := by nlinarith only [unit,chord,square]
    have coefficient := mul_nonneg (neg_nonneg.mpr nonpositive)
      (show 0≤17/20-c/2 by linarith only [cb.2.1])
    have formula : FC c s h r-(r-1)=1-a+z*(1-c/2) := by
      rw [FC,if_neg order]
      change (c/2)*z+a*s-(a-z)-(r-1)=_
      nlinarith only [rIdentity]
    nlinarith only [formula,gap,coefficient]

theorem FC_high_cap (c s h r : ℝ) (cn : Normal c s) (q : Quarter h r)
    (order : h≤r) : FC c s h r≤-h/2+(9/100)*r := by
  have first := mul_nonneg (sub_nonneg.mpr cn.2.1) q.sine
  have last := mul_nonneg cn.1 (sub_nonneg.mpr order)
  have cross : 0≤deltaC c s h r := by dsimp [deltaC]; nlinarith only [first,last]
  have envelope := C1092MPPMSteepPositiveNegativeProfile.Scalars.envelope cn
  dsimp [C1092MPPMSteepPositiveNegativeProfile.Scalars.f,
    C1092MPPMSteepPositiveNegativeProfile.Scalars.B] at envelope
  have weightA := mul_le_mul_of_nonneg_right
    (show -c+s-s^2≤-(1/2:ℝ) by linarith only [envelope.2]) q.cosine
  have weightB := mul_le_mul_of_nonneg_right
    (show 1+c*s-c-s≤9/100 by linarith only [envelope.1]) q.sine
  rw [FC_upper_formula cn cross]
  linarith only [weightA,weightB]

end
#print axioms FC_low_cap
#print axioms FC_middle_cap
#print axioms FC_high_cap
end N12Compact.C1092MPPMNegativeCrosspointSupport
