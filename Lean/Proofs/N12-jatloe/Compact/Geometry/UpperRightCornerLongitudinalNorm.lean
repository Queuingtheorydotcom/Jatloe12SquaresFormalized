import Compact.Geometry.C977CornerCubic

/-! A continuous norm certificate for the top-wall longitudinal support.
The rational half-angle parameter ranges over one interval. The quartic
lies below its endpoint chord throughout that interval. No angle list is
used. This source has not yet been compiled. -/
namespace N12Compact.UpperRightCornerLongitudinalNorm

open C977CornerCubic

private def quartic (z : ℝ) : ℝ :=
  -39551-315000*z+929102*z^2-885000*z^3+1720449*z^4

private theorem quartic_nonpos {z : ℝ} (zero : 0≤z) (bound : z≤3/7) :
    quartic z≤0 := by
  let q := 929102-885000*((3/7 : ℝ)+z)+
    1720449*((3/7 : ℝ)^2+(3/7)*z+z^2)
  have first : 0≤929102-885000*((3/7 : ℝ)+z) := by
    nlinarith only [bound]
  have rest : 0≤(3/7 : ℝ)^2+(3/7)*z+z^2 := by
    nlinarith only [zero,sq_nonneg z]
  have qp : 0≤q := by dsimp [q]; nlinarith only [first,rest]
  have left : quartic 0≤0 := by norm_num [quartic]
  have right : quartic (3/7)≤0 := by norm_num [quartic]
  have firstWeight := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤(3/7 : ℝ)-z by linarith only [bound]) left
  have lastWeight := mul_nonpos_of_nonneg_of_nonpos zero right
  have correction := mul_nonneg
    (mul_nonneg (mul_nonneg (show (0 : ℝ)≤3/7 by norm_num) zero)
      (show 0≤(3/7 : ℝ)-z by linarith only [bound])) qp
  have chord : (3/7 : ℝ)*quartic z=
      ((3/7 : ℝ)-z)*quartic 0+z*quartic (3/7)-
        (3/7)*z*((3/7)-z)*q := by
    dsimp [quartic,q]
    ring
  nlinarith only [chord,firstWeight,lastWeight,correction]

/-- The exact unit-circle residual in the longitudinal norm comparison. -/
theorem residual_nonpos {c s : ℝ} (normal : Normal c s) :
    261/100-(88/25)*c-(6/5)*s+(187949/250000)*c^2+
      (57/100)*c*s≤0 := by
  have bounds := normal_bounds normal
  have den : 0<1+c := by linarith only [bounds.1]
  have sine : s≤5/7 := by
    linarith only [normal.2.1,bounds.2.2.2.2.2]
  let z := s/(1+c)
  have zp : 0≤z := div_nonneg normal.1 den.le
  have zb : z≤3/7 := by
    apply (div_le_iff₀ den).mpr
    linarith only [sine,bounds.1]
  have zd : z*(1+c)=s := by dsimp [z]; field_simp [den.ne']
  clear_value z
  have zs : z*s=1-c := by
    have product := congrArg (fun x : ℝ => x*s) zd
    have identity : (1+c)*(z*s-(1-c))=0 := by
      nlinarith only [product,normal.2.2]
    exact sub_eq_zero.mp ((mul_eq_zero.mp identity).resolve_left den.ne')
  have square : z^2*(1+c)=1-c := by
    have product := congrArg (fun x : ℝ => z*x) zd
    nlinarith only [product,zs]
  have cform : (1+z^2)*c=1-z^2 := by
    nlinarith only [square]
  have sform : (1+z^2)*s=2*z := by
    have product := congrArg (fun x : ℝ => z*x) zs
    nlinarith only [product,zd]
  have identity : 250000*(1+z^2)^2*
      (261/100-(88/25)*c-(6/5)*s+(187949/250000)*c^2+
        (57/100)*c*s)=quartic z := by
    calc
      _ = 652500*(1+z^2)^2-880000*(1+z^2)*((1+z^2)*c)-
          300000*(1+z^2)*((1+z^2)*s)+187949*((1+z^2)*c)^2+
          142500*((1+z^2)*c)*((1+z^2)*s) := by ring
      _ = quartic z := by rw [cform,sform]; dsimp [quartic]; ring
  have poly := quartic_nonpos zp zb
  have scale : 0<250000*(1+z^2)^2 := by positivity
  exact nonpos_of_mul_nonpos_right (by rwa [identity]) scale

end N12Compact.UpperRightCornerLongitudinalNorm
