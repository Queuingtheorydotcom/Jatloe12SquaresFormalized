import Mathlib.Analysis.SpecialFunctions.Sqrt
import Compact.Completion.C1092.MPPMMissingPositiveBoundProfiles

/-! The sine-concavity step needed in sections 5.1 and 5.2, proved
algebraically on the whole upper unit-circle arc. The exact chord gap
factors into its two endpoint distances and one symmetric polynomial.
This includes zero endpoint values and the degenerate interval, without
adding an ODE or differentiability assumption. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMMissingPositiveBoundaries.Arc
open C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

def polynomial (q z r : ℝ) : ℝ :=
  (q+z+r)-(q^2+z^2+r^2)-(q*z+q*r+z*r)-
    ((q*z)^2+(q*r)^2+(z*r)^2)-q*z*r*(q+z+r)-q*z*r*(q*z+q*r+z*r)

theorem polynomial_nonneg (d q z r : ℝ)
    (dn : 0≤d) (diagonal : d^2+2*d=1)
    (qn : 0≤q) (qd : q≤d) (zn : 0≤z) (zd : z≤d) (rn : 0≤r) (rd : r≤d) :
    0≤polynomial q z r := by
  let S := q+z+r
  let P := q*z+q*r+z*r
  let R := q*z*r
  have Sn : 0≤S := by dsimp [S]; positivity
  have Pn : 0≤P := by dsimp [P]; positivity
  have Rn : 0≤R := by dsimp [R]; positivity
  have sqsum : q^2+z^2+r^2≤d*S := by
    have a := mul_nonneg qn (sub_nonneg.mpr qd)
    have b := mul_nonneg zn (sub_nonneg.mpr zd)
    have c := mul_nonneg rn (sub_nonneg.mpr rd)
    dsimp [S]
    nlinarith only [a,b,c]
  have pair : P≤d*S := by
    have a := mul_nonneg qn (sub_nonneg.mpr zd)
    have b := mul_nonneg zn (sub_nonneg.mpr qd)
    have c := mul_nonneg qn (sub_nonneg.mpr rd)
    have e := mul_nonneg rn (sub_nonneg.mpr qd)
    have f := mul_nonneg zn (sub_nonneg.mpr rd)
    have g := mul_nonneg rn (sub_nonneg.mpr zd)
    dsimp [P,S]
    nlinarith only [a,b,c,e,f,g]
  have qz : q*z≤d^2 := by nlinarith only [mul_le_mul qd zd zn dn]
  have qr : q*r≤d^2 := by nlinarith only [mul_le_mul qd rd rn dn]
  have zr : z*r≤d^2 := by nlinarith only [mul_le_mul zd rd rn dn]
  have triple : R≤d^3 := by
    have first := mul_le_mul_of_nonneg_right qz rn
    have last := mul_le_mul_of_nonneg_left rd (sq_nonneg d)
    dsimp [R]
    nlinarith only [first,last]
  have fourth : (q*z)^2+(q*r)^2+(z*r)^2≤d^3*S := by
    have a := mul_le_mul_of_nonneg_right qz (mul_nonneg qn zn)
    have b := mul_le_mul_of_nonneg_right qr (mul_nonneg qn rn)
    have c := mul_le_mul_of_nonneg_right zr (mul_nonneg zn rn)
    have last := mul_le_mul_of_nonneg_left pair (sq_nonneg d)
    dsimp [P] at last
    nlinarith only [a,b,c,last]
  have fourth' : R*S≤d^3*S := mul_le_mul_of_nonneg_right triple Sn
  have fifth : R*P≤d^4*S := by
    have first := mul_le_mul_of_nonneg_right triple Pn
    have last := mul_le_mul_of_nonneg_left pair (pow_nonneg dn 3)
    nlinarith only [first,last]
  have vanish : (1-2*d-2*d^3-d^4)*S=0 := by
    have factor : 1-2*d-2*d^3-d^4=(1+d^2)*(1-2*d-d^2) := by ring
    rw [factor,show 1-2*d-d^2=0 by linarith only [diagonal]]
    ring
  dsimp [polynomial]
  change 0≤S-(q^2+z^2+r^2)-P-((q*z)^2+(q*r)^2+(z*r)^2)-R*S-R*P
  nlinarith only [sqsum,pair,fourth,fourth',fifth,vanish]

def value (a A B z : ℝ) : ℝ :=
  (a/2)*(1+(cosH z)^2+sinH z*cosH z)+A*sinH z+B*cosH z

/-- Exact sine interpolation for a quadratic plus a linear support.
The normal is (sinH z,cosH z), and all three angles lie between the
vertical and the diagonal. Both endpoint hypotheses are weak. -/
theorem nonneg (d a A B q z r : ℝ)
    (dn : 0≤d) (diagonal : d^2+2*d=1) (an : 0≤a)
    (qn : 0≤q) (qz : q≤z) (zr : z≤r) (rd : r≤d)
    (left : 0≤value a A B q) (right : 0≤value a A B r) :
    0≤value a A B z := by
  by_cases equal : q=r
  · have zeq : z=q := by linarith only [qz,zr,equal]
    simpa only [zeq] using left
  have qr : q<r := lt_of_le_of_ne (qz.trans zr) equal
  have zn : 0≤z := qn.trans qz
  have rn : 0≤r := zn.trans zr
  have qd : q≤d := qz.trans (zr.trans rd)
  have zd : z≤d := zr.trans rd
  have leftDistance : 0≤z-q := sub_nonneg.mpr qz
  have rightDistance : 0≤r-z := sub_nonneg.mpr zr
  have length : 0<r-q := sub_pos.mpr qr
  let alpha := (r-z)*(1+r*z)*(1+q^2)/((r-q)*(1+r*q)*(1+z^2))
  let beta := (z-q)*(1+z*q)*(1+r^2)/((r-q)*(1+r*q)*(1+z^2))
  have den : 0<(r-q)*(1+r*q)*(1+z^2) := by positivity
  have alphaN : 0≤alpha := by dsimp [alpha]; positivity
  have betaN : 0≤beta := by dsimp [beta]; positivity
  have base : 0≤alpha*value a A B q+beta*value a A B r :=
    add_nonneg (mul_nonneg alphaN left) (mul_nonneg betaN right)
  have poly := polynomial_nonneg d q z r dn diagonal qn qd zn zd rn rd
  have gap : 0≤2*a*(z-q)*(r-z)*polynomial q z r := by positivity
  have scale : 0<(1+q*r)*(1+z^2)^2*(1+q^2)*(1+r^2) := by positivity
  have identity :
      ((1+q*r)*(1+z^2)^2*(1+q^2)*(1+r^2))*
        (value a A B z-alpha*value a A B q-beta*value a A B r)=
      2*a*(z-q)*(r-z)*polynomial q z r := by
    dsimp [value,alpha,beta,polynomial,cosH,sinH]
    field_simp [(sub_pos.mpr qr).ne',(half_den_pos q).ne',
      (half_den_pos z).ne',(half_den_pos r).ne',
      (show 1+r*q≠0 by positivity)]
    <;> ring
  have weighted : 0≤((1+q*r)*(1+z^2)^2*(1+q^2)*(1+r^2))*
      (value a A B z-alpha*value a A B q-beta*value a A B r) := by
    rw [identity]
    exact gap
  have comparison := nonneg_of_mul_nonneg_right weighted scale
  linarith only [base,comparison]

/-- The exact diagonal endpoint of the half-angle interval. -/
def diagonal : ℝ := Real.sqrt 2-1

theorem diagonal_data :
    0<diagonal ∧ diagonal<1/2 ∧ diagonal^2+2*diagonal=1 ∧
      cosH diagonal=Real.sqrt 2/2 ∧ sinH diagonal=Real.sqrt 2/2 := by
  have rp : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have rs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have low : 7/5<Real.sqrt 2 := by
    by_contra failed
    have product := mul_nonneg rp.le
      (show 0≤7/5-Real.sqrt 2 by linarith only [failed])
    nlinarith only [rp,rs,product,failed]
  have high : Real.sqrt 2<3/2 := by
    by_contra failed
    have product := mul_nonneg rp.le
      (show 0≤Real.sqrt 2-3/2 by linarith only [failed])
    nlinarith only [rp,rs,product,failed]
  have identity : diagonal^2+2*diagonal=1 := by dsimp [diagonal]; nlinarith only [rs]
  refine ⟨by dsimp [diagonal]; linarith only [low],
    by dsimp [diagonal]; linarith only [high],identity,?_,?_⟩
  · dsimp [cosH]
    apply (div_eq_iff (half_den_pos diagonal).ne').mpr
    change 1-diagonal^2=(Real.sqrt 2/2)*(1+diagonal^2)
    dsimp [diagonal]
    linear_combination -(Real.sqrt 2/2)*rs
  · dsimp [sinH]
    apply (div_eq_iff (half_den_pos diagonal).ne').mpr
    change 2*diagonal=(Real.sqrt 2/2)*(1+diagonal^2)
    dsimp [diagonal]
    linear_combination (1-Real.sqrt 2/2)*rs

end
end N12Compact.C1092MPPMMissingPositiveBoundaries.Arc
