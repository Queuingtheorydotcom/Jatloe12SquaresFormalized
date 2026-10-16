import Compact.Completion.C1092.MPPMCrosspointQuadraticRemainders
import Compact.Completion.C1092.MPPMCrosspointBoundaryG10Clamp

/-! Closed half-angle coordinates for the boundary-scalar joins. -/
namespace N12Compact.C1092MPPMCrosspointSupport
open C977CornerCubic C977CornerSectorBounds C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

def half (c s : ℝ) : ℝ := s/(1+c)
abbrev rho := C1092MPPMMissingPositiveBoundaries.Arc.diagonal

theorem quarter_half {c s : ℝ} (q : Quarter c s) :
    0≤half c s ∧ half c s≤1 ∧ cosH (half c s)=c ∧ sinH (half c s)=s := by
  let z := half c s
  have den : 0<1+c := by linarith only [q.cosine]
  have zn : 0≤z := div_nonneg q.sine den.le
  have sh : s≤1 := by nlinarith only [q.unit,sq_nonneg c,sq_nonneg (s-1)]
  have zh : z≤1 := by
    apply (div_le_iff₀ den).mpr
    linarith only [sh,q.cosine]
  have relation : z*(1+c)=s := div_mul_cancel₀ _ den.ne'
  have halfIdentity : s*z=1-c := by
    apply mul_right_cancel₀ den.ne'
    linear_combination s*relation+q.unit
  have hc : cosH z=c := by
    apply (div_eq_iff (half_den_pos z).ne').mpr
    linear_combination -z*relation-halfIdentity
  have hs : sinH z=s := by
    apply (div_eq_iff (half_den_pos z).ne').mpr
    linear_combination relation-z*halfIdentity
  exact ⟨zn,zh,hc,hs⟩

theorem rho_bounds : 0<rho ∧ rho<5/12 ∧ rho^2+2*rho=1 ∧
    cosH rho=Real.sqrt 2/2 ∧ sinH rho=Real.sqrt 2/2 := by
  have data := C1092MPPMMissingPositiveBoundaries.Arc.diagonal_data
  have upper : rho<5/12 := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg (show 0≤rho-5/12 by linarith only [bad])
      (show 0≤rho+5/12+2 by linarith only [data.1])
    nlinarith only [product,data.2.2.1]
  exact ⟨data.1,upper,data.2.2.1,data.2.2.2.1,data.2.2.2.2⟩

theorem normal_half {c s : ℝ} (cn : Normal c s) :
    0≤half c s ∧ half c s≤rho ∧ 0≤1-2*half c s-(half c s)^2 ∧
      cosH (half c s)=c ∧ sinH (half c s)=s := by
  have cb := normal_bounds cn
  have data := quarter_half (show Quarter c s from ⟨by linarith only [cb.1],cn.1,cn.2.2⟩)
  have diagonal : 0≤1-2*half c s-(half c s)^2 := by
    have product := mul_nonneg (sub_nonneg.mpr cn.2.1) (half_den_pos (half c s)).le
    have identity : (c-s)*(1+(half c s)^2)=1-2*half c s-(half c s)^2 := by
      have cosine : 1-(half c s)^2=c*(1+(half c s)^2) :=
        (div_eq_iff (half_den_pos (half c s)).ne').mp data.2.2.1
      have sine : 2*half c s=s*(1+(half c s)^2) :=
        (div_eq_iff (half_den_pos (half c s)).ne').mp data.2.2.2
      nlinarith only [cosine,sine]
    rw [←identity]
    exact product
  have rb := rho_bounds
  have upper : half c s≤rho := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (sub_pos.mpr bad)
      (show 0<half c s+rho+2 by linarith only [data.1,rb.1])
    nlinarith only [product,diagonal,rb.2.2.1]
  exact ⟨data.1,upper,diagonal,data.2.2.1,data.2.2.2⟩

theorem half_order {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (order : s≤t) : half c s≤half d t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cosine := cosine_order en cn order
  apply (div_le_div_iff₀ (by linarith only [cb.1]) (by linarith only [eb.1])).mpr
  have first := mul_nonneg (sub_nonneg.mpr order)
    (show 0≤1+c by linarith only [cb.1])
  have last := mul_nonneg cn.1 (sub_nonneg.mpr cosine)
  nlinarith only [first,last]

theorem steep_half {c s : ℝ} (cn : Normal c s) (steep : 3/5≤s) :
    1/3≤half c s := by
  have cb := normal_bounds cn
  have bound := steep_bounds cn steep
  apply (le_div_iff₀ (by linarith only [cb.1] : 0<1+c)).mpr
  linarith only [bound.1,steep]

end
end N12Compact.C1092MPPMCrosspointSupport
