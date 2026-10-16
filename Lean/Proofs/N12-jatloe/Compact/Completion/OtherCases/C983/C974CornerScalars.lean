import Compact.Completion.C1092.WallProfileScalars
import Compact.Completion.C981.SupportForms

/-! Exact scalar identities in C974-THREE-SQUARE-ENDING §§3–4.
The four cubic coefficients are copied from the completed continuous
argument, with no angle subdivision or generated certificate. -/
namespace N12Compact.Completion.OtherCases.C983.C974CornerScalars
set_option Elab.async false

theorem normal_forms (c s : ℝ) (cn : 0≤c) (sn : 0≤s) (unit : c^2+s^2=1) :
    let z := s/(1+c)
    0≤z ∧ z≤1 ∧ c=(1-z^2)/(1+z^2) ∧ s=2*z/(1+z^2) := by
  have data := C1092WallProfileScalars.quarter_data c s cn sn unit
  let z := s/(1+c)
  have denominator : 1+z^2≠0 := by positivity
  refine ⟨data.1,data.2.1,?_,?_⟩
  · apply (eq_div_iff denominator).mpr
    simpa only [z,C1092WallProfileScalars.half,mul_comm] using data.2.2.2.1
  · apply (eq_div_iff denominator).mpr
    simpa only [z,C1092WallProfileScalars.half,mul_comm] using data.2.2.2.2

/-- Equation (27), with all four coefficients strictly positive. -/
theorem cubic_gap (d t z c s w : ℝ) (zp : 0<z) (zu : z<1/3)
    (order : z≤w) (wu : w≤1)
    (dform : d=(1-z^2)/(1+z^2)) (tform : t=2*z/(1+z^2))
    (cform : c=(1-w^2)/(1+w^2)) (sform : s=2*w/(1+w^2)) :
    0<(1-t/2)*(c*d+s*t)-1+w := by
  let v := (w-z)/(1-z)
  let b0 := z^3*(1+z^2)^2
  let b1 := (1+z^2)*(1+z+z^2)*(3*z^2-2*z+1)/3
  let b2 := 2*z*(2*z^4-z^3+5*z^2-3*z+3)/3
  let b3 := 4*z*(z^2-z+1)
  have rest : 0<1-z := by linarith only [zu]
  have vn : 0≤v := div_nonneg (sub_nonneg.mpr order) rest.le
  have vu : v≤1 := (div_le_one rest).mpr (by linarith only [wu])
  have b0p : 0<b0 := by dsimp only [b0]; positivity
  have b1p : 0<b1 := by
    have quadratic : 0<3*z^2-2*z+1 := by nlinarith only [sq_nonneg (z-1/3)]
    dsimp only [b1]
    positivity
  have b2p : 0<b2 := by
    have smallCube := mul_nonneg (sq_nonneg z) (show 0≤1/3-z by linarith only [zu])
    have polynomial : 0<2*z^4-z^3+5*z^2-3*z+3 := by
      nlinarith only [smallCube,zu,sq_nonneg z,pow_nonneg zp.le 4]
    dsimp only [b2]
    positivity
  have b3p : 0<b3 := by
    have quadratic : 0<z^2-z+1 := by nlinarith only [sq_nonneg (z-1/2)]
    dsimp only [b3]
    positivity
  have polynomial : 0<b0*(1-v)^3+3*b1*v*(1-v)^2+
      3*b2*v^2*(1-v)+b3*v^3 := by
    rcases vu.eq_or_lt with endPoint | interior
    · rw [endPoint]
      simpa using b3p
    · have remaining : 0<1-v := sub_pos.mpr interior
      positivity
  have zn : 1+z^2≠0 := by positivity
  have wn : 1+w^2≠0 := by positivity
  have identity : (1+z^2)^2*(1+w^2)*((1-t/2)*(c*d+s*t)-1+w)=
      b0*(1-v)^3+3*b1*v*(1-v)^2+3*b2*v^2*(1-v)+b3*v^3 := by
    rw [dform,tform,cform,sform]
    dsimp only [b0,b1,b2,b3,v]
    field_simp [zn,wn,rest.ne']
    ring
  have factor : 0<(1+z^2)^2*(1+w^2) := by positivity
  apply lt_of_not_ge
  intro bad
  have impossible := mul_nonpos_of_nonneg_of_nonpos factor.le bad
  linarith only [impossible,identity,polynomial]

/-- The last angular sector's exact estimate (28). -/
theorem steep_gain (d t : ℝ) (dp : 4/5<d) (tp : 0<t) (ts : t<3/5)
    (unit : d^2+t^2=1) : 1<(d+(3/2)*t)*(1-t/2) := by
  have du : d≤1 := by nlinarith only [unit,sq_nonneg t,dp]
  have factor := mul_nonneg (show 0≤1-d by linarith only [du])
    (show 0≤1+d-9/5 by linarith only [dp])
  have low : -(5/9)*t^2≤d-1 := by nlinarith only [factor,unit]
  have first := mul_nonneg tp.le (sub_nonneg.mpr du)
  have positive := mul_pos tp (show 0<1-(47/36)*t by linarith only [ts])
  nlinarith only [low,first,positive]

end N12Compact.Completion.OtherCases.C983.C974CornerScalars
