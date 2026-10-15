import Compact.Completion.C1092.MPPMCrosspointSupportScalars
import Mathlib.Tactic.FieldSimp

/-! Exact lower endpoint polynomial in STEEP-POSITIVE-BOUNDARY-SCALARS
section7. The cubic is written directly in a positive Bernstein basis;
neither derivative estimates nor angle samples are needed. Source only. -/
namespace N12Compact.C1092MPPMCrosspointSupport
set_option Elab.async false
noncomputable section

private theorem lower_identity (h r z : ℝ)
    (hc : h=(1-z^2)/(1+z^2)) (rs : r=2*z/(1+z^2)) :
    (h+2*r-2+(3496/3125)*h^2-(1+11387/12500)*h*r+(14/25)*r^2-1/3125)*
      (1+z^2)^2 =
      (1-3*z)*(3920*z^3-14989*z^2+3333*z+740)/6250 := by
  rw [hc,rs]
  have denominator : 1+z^2≠0 := by positivity
  field_simp [denominator]
  ring

theorem lower_endpoint_D (h r : ℝ) (q : Quarter h r)
    (hh : 4/5≤h) (hr : r≤3/5) :
    1/3125≤h+2*r-2+(3496/3125)*h^2-(1+11387/12500)*h*r+(14/25)*r^2 := by
  let z := r/(1+h)
  have hd : 0<1+h := by linarith only [hh]
  have zn : 0≤z := div_nonneg q.sine hd.le
  have zu : z≤1/3 := by
    apply (div_le_iff₀ hd).mpr
    linarith only [hh,hr]
  have relation : z*(1+h)=r := div_mul_cancel₀ _ hd.ne'
  have half : r*z=1-h := by
    apply mul_right_cancel₀ hd.ne'
    linear_combination r*relation+q.unit
  have hc : h=(1-z^2)/(1+z^2) := by
    apply (eq_div_iff (by positivity : (1+z^2:ℝ)≠0)).mpr
    linear_combination z*relation+half
  have rs : r=2*z/(1+z^2) := by
    apply (eq_div_iff (by positivity : (1+z^2:ℝ)≠0)).mpr
    linear_combination z*half-relation
  have gap : 0≤1/3-z := sub_nonneg.mpr zu
  have cubic : 0≤3920*z^3-14989*z^2+3333*z+740 := by
    have identity : 3920*z^3-14989*z^2+3333*z+740 =
        19980*(1/3-z)^3+89937*z*(1/3-z)^2+
          74967*z^2*(1/3-z)+8930*z^3 := by ring
    rw [identity]
    positivity
  have numerator : 0≤(1-3*z)*(3920*z^3-14989*z^2+3333*z+740)/6250 :=
    div_nonneg (mul_nonneg (by linarith only [zu]) cubic) (by norm_num)
  rw [←lower_identity h r z hc rs] at numerator
  have denominator : 0<(1+z^2)^2 := by positivity
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left numerator denominator)

end
#print axioms lower_endpoint_D
end N12Compact.C1092MPPMCrosspointSupport
