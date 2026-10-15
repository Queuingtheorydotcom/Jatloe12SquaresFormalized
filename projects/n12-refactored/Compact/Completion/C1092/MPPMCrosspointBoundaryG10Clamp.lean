import Compact.Completion.C1092.MPPMCrosspointSupportScalars
import Compact.Completion.C1092.MPPMSteepPositiveSuccessorFarCapScalars

/-! The clamped C support from BOUNDARY-SCALARS section 5, proved by
unit-circle products. The upper endpoint is weakened to the rational
coefficient .129; this suffices for both boundary support estimates. -/
namespace N12Compact.C1092MPPMCrosspointSupport
open C977CornerCubic
set_option Elab.async false

theorem steep_bounds {c s : ℝ} (cn : Normal c s) (steep : 3/5≤s) :
    c≤4/5 ∧ s<71/100 ∧ 7/5≤c+s ∧ c+s<14143/10000 := by
  have cb := C1092MPPMPositiveRetainingSteep.Scalars.canonical_bounds cn
  have cosine := C1092MMMPUpperThirdScalars.cosine_cap cn steep
  have product := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr steep)
    (show s-4/5≤0 by linarith only [cb.2.2.2.1])
  have lower : 7/5≤c+s := by
    apply le_of_not_gt
    intro no
    have square := mul_pos (show 0<7/5-s-c by linarith only [no])
      (show 0<7/5-s+c by linarith only [no,cb.1])
    nlinarith only [square,product,cn.2.2]
  have upper : c+s<14143/10000 := by
    apply lt_of_not_ge
    intro no
    have square := mul_nonneg (show 0≤c+s-14143/10000 by linarith only [no])
      (show 0≤c+s+14143/10000 by linarith only [cb.1,cn.1])
    nlinarith only [square,sq_nonneg (c-s),cn.2.2]
  exact ⟨cosine,cb.2.2.2.1,lower,upper⟩

theorem FC_lower_formula {c s h r : ℝ} (cn : Normal c s)
    (order : deltaC c s h r≤0) :
    FC c s h r=(-c-s+(293/500)*c*s)*h+
      (c-s+c^2/2+(543/500)*s^2)*r := by
  by_cases branch : 0≤deltaC c s h r
  · have zero : deltaC c s h r=0 := le_antisymm order branch
    simp only [FC,if_pos branch]
    dsimp [kC,deltaC] at zero ⊢
    linear_combination (c+s-c/2-2)*zero
  · simp only [FC,if_neg branch]
    dsimp [kC,deltaC]
    ring

theorem FC_upper_formula {c s h r : ℝ} (cn : Normal c s)
    (order : 0≤deltaC c s h r) :
    FC c s h r=(-c+s+(43/500)*c*s-s^2)*h+
      (1+(43/500)*s^2+c*s-c-s)*r := by
  simp only [FC,if_pos order]
  dsimp [kC,deltaC]
  linear_combination r*cn.2.2

theorem FC_low_cap (c s h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (q : Quarter h r) (hh : 4/5≤h) (rr : r≤3/5) :
    FC c s h r≤-(3496/3125)*h+(11387/12500)*r := by
  have cb := normal_bounds cn
  have b := steep_bounds cn steep
  have first := mul_nonneg (show 0≤c by linarith only [cb.1])
    (show 0≤3/5-r by linarith only [rr])
  have last := mul_nonneg cn.1 (show 0≤h-4/5 by linarith only [hh])
  have order : deltaC c s h r≤0 := by
    dsimp [deltaC]
    nlinarith only [first,last,b.1,steep]
  have sumProduct := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤c+s-7/5 by linarith only [b.2.2.1])
    (show -1+(293/1000)*(c+s+7/5)≤0 by linarith only [b.2.2.2])
  have lowA : -c-s+(293/500)*c*s≤-(3496/3125) := by
    nlinarith only [sumProduct,cn.2.2]
  have sineProduct := mul_nonneg (sub_nonneg.mpr steep)
    (show 0≤1-(293/500)*(s+3/5) by linarith only [b.2.1])
  have lowB : c-s+c^2/2+(543/500)*s^2≤11387/12500 := by
    nlinarith only [sineProduct,b.1,cn.2.2]
  have a := mul_le_mul_of_nonneg_right lowA q.cosine
  have z := mul_le_mul_of_nonneg_right lowB q.sine
  rw [FC_lower_formula cn order]
  linarith only [a,z]

theorem FC_middle_cap (c s h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (bn : Normal h r) (bs : 3/5≤r) : FC c s h r≤(543/500)*r-1 := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have ccap := steep_bounds cn steep
  have bcap := steep_bounds bn bs
  let a := kC c s h r
  let z := deltaC c s h r
  have ap : 0<a := by
    have first := mul_pos (show 0<c by linarith only [cb.1])
      (show 0<h by linarith only [bb.1])
    have last := mul_nonneg cn.1 bn.1
    dsimp [a,kC]
    nlinarith only [first,last]
  have ah : a≤1 := by
    dsimp [a,kC]
    exact C977CornerSectorBounds.dot_le_one cn bn
  have unit : a^2+z^2=1 := by
    dsimp [a,z,kC,deltaC]
    linear_combination (h^2+r^2)*cn.2.2+bn.2.2
  have rIdentity : r=a*s+z*c := by
    dsimp [a,z,kC,deltaC]
    linear_combination -r*cn.2.2
  have chord := mul_nonneg ap.le (show 0≤1-a by linarith only [ah])
  by_cases order : 0≤z
  · have first := mul_nonneg cn.1 (sub_nonneg.mpr bn.2.1)
    have last := mul_nonneg bn.1 (show 0≤1/5-(c-s) by linarith only [ccap.1,steep])
    have small : z<3/20 := by dsimp [z,deltaC]; nlinarith only [first,last,bcap.2.1]
    have square := mul_nonneg order (show 0≤3/20-z by linarith only [small])
    have gap : 1-a≤(3/20)*z := by nlinarith only [unit,chord,square]
    have coefficient := mul_nonneg order
      (show 0≤17/20+(43/500)*c-s by linarith only [cb.1,ccap.2.1])
    have formula : FC c s h r-((543/500)*r-1)=1-a+z*(s-1-(43/500)*c) := by
      have branch : 0≤deltaC c s h r := order
      simp only [FC,if_pos branch]
      change z*(c+s)+a*(543/500)*s-(a+z)-((543/500)*r-1)=_
      nlinarith only [rIdentity]
    nlinarith only [formula,gap,coefficient]
  · have branch : ¬0≤deltaC c s h r := order
    have order : z≤0 := (lt_of_not_ge order).le
    have first := mul_nonneg bn.1 (sub_nonneg.mpr cn.2.1)
    have last := mul_nonneg cn.1 (show 0≤1/5-(h-r) by linarith only [bcap.1,bs])
    have small : -z<3/20 := by dsimp [z,deltaC]; nlinarith only [first,last,ccap.2.1]
    have square := mul_nonneg (neg_nonneg.mpr order)
      (show 0≤3/20+z by linarith only [small])
    have gap : 1-a≤-(3/20)*z := by nlinarith only [unit,chord,square]
    have coefficient := mul_nonneg (neg_nonneg.mpr order)
      (show 0≤17/20-(293/500)*c by linarith only [ccap.1])
    have formula : FC c s h r-((543/500)*r-1)=1-a+z*(1-(293/500)*c) := by
      simp only [FC,if_neg branch]
      change (c/2)*z+a*(543/500)*s-(a-z)-((543/500)*r-1)=_
      nlinarith only [rIdentity]
    nlinarith only [formula,gap,coefficient]

theorem FC_high_cap (c s h r : ℝ) (cn : Normal c s) (steep : 3/5≤s)
    (q : Quarter h r) (order : h≤r) :
    FC c s h r≤-(457/1000)*h+(129/1000)*r := by
  have cb := normal_bounds cn
  have b := steep_bounds cn steep
  have first := mul_nonneg (sub_nonneg.mpr cn.2.1) q.sine
  have last := mul_nonneg cn.1 (sub_nonneg.mpr order)
  have branch : 0≤deltaC c s h r := by dsimp [deltaC]; nlinarith only [first,last]
  have product := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤1-(c+s)/2 by linarith only [b.2.2.2])
  have a : -c+s+(43/500)*c*s-s^2≤-(457/1000) := by
    nlinarith only [product,sq_nonneg (c-s),cn.2.2]
  have sumProduct := mul_nonneg (show 0≤14143/10000-(c+s) by linarith only [b.2.2.2])
    (show 0≤14143/10000+(c+s)-2 by linarith only [b.2.2.1])
  have normalProduct := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤c+s by linarith only [cb.1,cn.1])
  have z : 1+(43/500)*s^2+c*s-c-s≤129/1000 := by
    nlinarith only [sumProduct,normalProduct,cn.2.2]
  have ah := mul_le_mul_of_nonneg_right a q.cosine
  have zr := mul_le_mul_of_nonneg_right z q.sine
  rw [FC_upper_formula cn branch]
  linarith only [ah,zr]

end N12Compact.C1092MPPMCrosspointSupport
