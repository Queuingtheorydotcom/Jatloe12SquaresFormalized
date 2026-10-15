import Compact.Completion.C1092.MPPMInwardFinalAngleScalars
import Mathlib.Data.Real.Sqrt

/-! INWARD-OUTER-OWNED-ANGLE: exact unit-circle identities and the
entire half-angle interval. No sampled angle or numerical search is used.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false

theorem outer_short_width {c s : ℝ} (unit : c^2+s^2=1) :
    (37/50)*c+(3/5)*s<1 ∧ (3/5)*c+(37/50)*s<1 := by
  constructor
  · nlinarith only [unit,sq_nonneg ((3/5)*c-(37/50)*s),
      sq_nonneg ((37/50)*c+(3/5)*s-1)]
  · nlinarith only [unit,sq_nonneg ((37/50)*c-(3/5)*s),
      sq_nonneg ((3/5)*c+(37/50)*s-1)]

theorem outer_lower_half {c s : ℝ} (cn : Normal c s)
    (width : 1<c+(13/50)*s) : half c s<13/50 := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let z := half c s
  have den : 0<1+z^2 := by nlinarith only [sq_nonneg z]
  have identity : (1+z^2)*(c+(13/50)*s-1)=2*z*(13/50-z) := by
    nlinarith only [data.2.2.2.1,data.2.2.2.2]
  have positive := mul_pos den (sub_pos.mpr width)
  apply lt_of_not_ge
  intro no
  have bad := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤2*z by linarith only [data.1]) (show 13/50-z≤0 by exact sub_nonpos.mpr no)
  nlinarith only [identity,positive,bad]

theorem outer_upper_slope {c s : ℝ} (cn : Normal c s)
    (width : 1<(37/50)*(c+s)) : c<2*s := by
  have cb := normal_bounds cn
  apply lt_of_not_ge
  intro no
  have product := mul_nonneg
    (show 0≤2*c-s by linarith only [cn.1,cn.2.1])
    (show 0≤c-2*s by linarith only [no])
  have strict := mul_pos
    (show 0<c+s-50/37 by linarith only [width])
    (show 0<c+s+50/37 by linarith only [cb.1,cn.1])
  nlinarith only [product,strict,cn.2.2]

theorem outer_q_identity {c s : ℝ} (cn : Normal c s) :
    (1+(half c s)^2)*(1-c+(13/50)*s-half c s)=
      -(half c s)*((half c s)^2-2*half c s+12/25) ∧
    c+s-1-c*s+(13/50)*s^2=s*(1-c+(13/50)*s-half c s) := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  have zero : (1+c)*(c-1+s*half c s)=0 := by
    linear_combination cn.2.2+s*data.2.2.1
  have relation : c-1+s*half c s=0 :=
    (mul_eq_zero.mp zero).resolve_left (by linarith only [cb.1])
  constructor
  · nlinarith only [data.2.2.2.1,data.2.2.2.2]
  · nlinarith only [relation]

/-- This is the literal radical bound, with rational consequences used
by the later physical comparison. Equality at the radical is excluded. -/
theorem outer_angle_bounds {c s : ℝ} (cn : Normal c s)
    (polynomial : 0<(half c s)^2-2*half c s+12/25) :
    half c s<1-Real.sqrt 13/5 ∧ half c s<279/1000 ∧
      17/20<c ∧ s<13/25 := by
  have cb := normal_bounds cn
  have zb := canonical_half_bounds cn
  let z := half c s
  have rootPositive : 0<Real.sqrt 13 := Real.sqrt_pos.2 (by norm_num)
  have rootSquare : (Real.sqrt 13)^2=13 := Real.sq_sqrt (by norm_num)
  have exactBound : z<1-Real.sqrt 13/5 := by
    apply lt_of_not_ge
    intro no
    have product := mul_nonneg
      (show 0≤Real.sqrt 13/5-(1-z) by linarith only [no])
      (show 0≤Real.sqrt 13/5+(1-z) by linarith only [rootPositive,zb.2])
    nlinarith only [product,rootSquare,polynomial]
  have rational : z<279/1000 := by
    apply lt_of_not_ge
    intro no
    have product := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤z-279/1000 by exact sub_nonneg.mpr no)
      (show z+279/1000-2≤0 by linarith only [zb.2])
    nlinarith only [product,polynomial]
  have endpoint : Normal (922159/1077841) (558000/1077841) := by norm_num [Normal]
  have endpointHalf : half (922159/1077841) (558000/1077841)=279/1000 := by
    norm_num [half]
  have cross := half_cross cn endpoint (by simpa only [endpointHalf] using rational.le)
  have coordinates := coordinates_after endpoint cn cross
  exact ⟨exactBound,rational,by linarith only [coordinates.1],
    by linarith only [coordinates.2]⟩

theorem outer_halfpoint_projection {c s : ℝ} (cn : Normal c s)
    (small : half c s<1/3) : s+c/2<1 := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let z := half c s
  have identity : (1+z^2)*(1-s-c/2)=(1/2)*(1-z)*(1-3*z) := by
    nlinarith only [data.2.2.2.1,data.2.2.2.2]
  have positive := mul_pos
    (mul_pos (by norm_num : (0:ℝ)<1/2) (show 0<1-z by linarith only [small]))
    (show 0<1-3*z by linarith only [small])
  have scaled : 0<(1+z^2)*(1-s-c/2) := by rw [identity]; exact positive
  have unscaled := pos_of_mul_pos_right scaled (by nlinarith only [sq_nonneg z] : 0≤1+z^2)
  linarith only [unscaled]

#print axioms outer_angle_bounds
end N12Compact.C1092MPPMInwardFinal
