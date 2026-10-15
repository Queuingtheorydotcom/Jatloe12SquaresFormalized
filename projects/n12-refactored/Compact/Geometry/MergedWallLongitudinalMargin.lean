import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! The final longitudinal scalar for an escaping merged central pair.
The wall marker and the actual container give two upper supports. Two
continuous ranges of the wall cosine suffice. The large-cosine range
uses the explicit divided difference of a quartic, not sampled angles. -/
namespace N12Compact.MergedWallLongitudinalMargin
set_option Elab.async false

private noncomputable def leftPoly (z : ℝ) : ℝ :=
  -(43/500)-(7/10)*z-(193/250)*z^2+(7/10)*z^3-(1043/500)*z^4

private noncomputable def rightPoly (z : ℝ) : ℝ :=
  7/20+(13/10)*z-(7/10)*z^2+(27/10)*z^3+(7/20)*z^4

private noncomputable def markerNumerator (r t z : ℝ) : ℝ := r*leftPoly z+t*rightPoly z

private noncomputable def wallNumerator (r t z : ℝ) : ℝ :=
  r*markerNumerator r t z+(r-457/500)*(1+z^2)^2

private theorem small_cosine (r t z : ℝ) (hr : 0 < r) (ht : 0 ≤ t)
    (normal : r^2+t^2=1) (small : r ≤ 457/500)
    (hz : 0 ≤ z) (zhi : z ≤ 1/5) : 0 ≤ markerNumerator r t z := by
  have ratio : (11/25)*r ≤ t := by
    by_contra failure
    have strict := lt_of_not_ge failure
    have square := mul_pos (sub_pos.mpr strict)
      (show 0 < (11/25)*r+t by linarith only [hr,ht])
    have bound := mul_nonneg (sub_nonneg.mpr small)
      (show 0 ≤ 457/500+r by linarith only [hr])
    nlinarith only [square,bound,normal]
  have rb : 0 ≤ rightPoly z := by
    have quadratic := mul_nonneg hz
      (show 0 ≤ 13/10-(7/10)*z by linarith only [zhi])
    have cubic := mul_nonneg hz (sq_nonneg z)
    dsimp [rightPoly]
    nlinarith only [quadratic,cubic,sq_nonneg (z^2)]
  have bernstein : leftPoly z+(11/25)*rightPoly z =
      (17/250)*(1-5*z)^4+
      4*(77/1250)*(5*z)*(1-5*z)^3+
      6*(6/125)*(5*z)^2*(1-5*z)^2+
      4*(484/15625)*(5*z)^3*(1-5*z)+
      (876/78125)*(5*z)^4 := by
    dsimp [leftPoly,rightPoly]
    ring
  have rest : 0 ≤ 1-5*z := by linarith only [zhi]
  have central : 0 ≤ leftPoly z+(11/25)*rightPoly z := by
    rw [bernstein]
    positivity
  have first := mul_nonneg hr.le central
  have second := mul_nonneg (sub_nonneg.mpr ratio) rb
  dsimp [markerNumerator]
  nlinarith only [first,second]

/-- The displayed coefficient bound implies that the quartic lies above
its endpoint chord throughout [0,Z]. The identity is the exact divided
difference and is valid also at either endpoint. -/
private theorem quartic_chord (a₀ a₁ a₂ a₃ a₄ z Z : ℝ)
    (hz : 0 ≤ z) (hzZ : z ≤ Z) (hZ : 0 < Z) (Zhi : Z ≤ 1/5)
    (a₃pos : 0 ≤ a₃) (a₄neg : a₄ ≤ 0) (curve : a₂+(2/5)*a₃ ≤ 0)
    (left : 0 ≤ a₀) (right : 0 ≤ a₀+a₁*Z+a₂*Z^2+a₃*Z^3+a₄*Z^4) :
    0 ≤ a₀+a₁*z+a₂*z^2+a₃*z^3+a₄*z^4 := by
  have sum : z+Z ≤ 2/5 := by linarith only [hzZ,Zhi]
  have cubic := mul_nonneg a₃pos (sub_nonneg.mpr sum)
  have zz : 0 ≤ z^2+z*Z+Z^2 := by positivity
  have fourth := mul_nonpos_of_nonpos_of_nonneg a₄neg zz
  have bracket : a₂+a₃*(z+Z)+a₄*(z^2+z*Z+Z^2) ≤ 0 := by
    nlinarith only [curve,cubic,fourth]
  have one := mul_nonneg (sub_nonneg.mpr hzZ) left
  have two := mul_nonneg hz right
  have three := mul_nonneg (mul_nonneg hZ.le
    (mul_nonneg hz (sub_nonneg.mpr hzZ))) (neg_nonneg.mpr bracket)
  have identity : Z*(a₀+a₁*z+a₂*z^2+a₃*z^3+a₄*z^4) =
      (Z-z)*a₀+z*(a₀+a₁*Z+a₂*Z^2+a₃*Z^3+a₄*Z^4)+
      Z*z*(Z-z)*(-(a₂+a₃*(z+Z)+a₄*(z^2+z*Z+Z^2))) := by ring
  nlinarith only [one,two,three,identity,hZ]

private theorem large_cosine (r t z : ℝ) (hr : 0 < r) (ht : 0 ≤ t)
    (normal : r^2+t^2=1) (large : 457/500 ≤ r) (hz : 0 ≤ z)
    (wall : r*t*z < 1-r-(43/500)*t^2) : 0 ≤ wallNumerator r t z := by
  have rone : r ≤ 1 := by nlinarith only [normal,sq_nonneg t,hr]
  have tp : 0 < t := by
    by_contra failure
    have zero : t=0 := le_antisymm (le_of_not_gt failure) ht
    rw [zero] at normal wall
    nlinarith only [normal,wall,hr]
  have ratio : t ≤ (9/20)*r := by
    by_contra failure
    have strict := lt_of_not_ge failure
    have square := mul_pos (sub_pos.mpr strict)
      (show 0 < t+(9/20)*r by linarith only [hr,ht])
    have bound := mul_nonneg (sub_nonneg.mpr large)
      (show 0 ≤ r+457/500 by linarith only [hr])
    nlinarith only [square,bound,normal]
  let Z := (1-r-(43/500)*t^2)/(r*t)
  have den : 0 < r*t := mul_pos hr tp
  have root : r*t*Z=1-r-(43/500)*t^2 := by
    dsimp [Z]
    field_simp [ne_of_gt den]
  have zZ : z < Z := (lt_div_iff₀ den).mpr (by nlinarith only [wall])
  have Zpos : 0 < Z := lt_of_le_of_lt hz zZ
  have relation : r*(1+r)*Z=t*(457/500-(43/500)*r) := by
    apply (mul_left_cancel₀ (ne_of_gt tp))
    linear_combination (1+r)*root-normal
  have coefficient : 457/500-(43/500)*r ≤ (11/25)*(1+r) := by
    linarith only [large]
  have coefficient' : 457/500-(43/500)*r ≤ r := by
    linarith only [large]
  have bound₁ := mul_nonneg ht (sub_nonneg.mpr coefficient)
  have bound₂ := mul_nonneg (show 0 ≤ (11/25)*(1+r) by positivity)
    (sub_nonneg.mpr ratio)
  have Zbound : Z ≤ 99/500 := by
    have positive : 0 < r*(1+r) := by positivity
    nlinarith only [relation,bound₁,bound₂,positive]
  have Zhi : Z ≤ 1/5 := by linarith only [Zbound]
  have half : (1+r)*Z ≤ t := by
    have bound := mul_nonneg ht (sub_nonneg.mpr coefficient')
    nlinarith only [relation,bound,hr]
  have cross : 0 ≤ t*(1-Z^2)-2*r*Z := by
    have product := mul_nonneg (sub_nonneg.mpr half)
      (show 0 ≤ 1+r+t*Z by positivity)
    have identity : (1+r)*(t*(1-Z^2)-2*r*Z) =
        (t-(1+r)*Z)*(1+r+t*Z) := by
      linear_combination -Z*normal
    nlinarith only [product,identity,hr]
  have bracket : 0 ≤ Z*(1+Z^2)+(7/20)*(1-2*Z-Z^2) := by
    have square := mul_nonneg Zpos.le (sub_nonneg.mpr Zhi)
    have cubic := mul_nonneg Zpos.le (sq_nonneg Z)
    nlinarith only [square,cubic,Zpos,Zhi]
  have endpoint : 0 ≤ wallNumerator r t Z := by
    have identity : wallNumerator r t Z =
        r*(t*(1-Z^2)-2*r*Z)*(Z*(1+Z^2)+(7/20)*(1-2*Z-Z^2)) := by
      dsimp [wallNumerator,markerNumerator,leftPoly,rightPoly]
      linear_combination (1+Z^2)^2*root-(43/500)*(1+Z^2)^2*normal
    rw [identity]
    exact mul_nonneg (mul_nonneg hr.le cross) bracket
  have start : 0 ≤ wallNumerator r t 0 := by
    have identity : wallNumerator r t 0 = r*t*(7/20-Z) := by
      dsimp [wallNumerator,markerNumerator,leftPoly,rightPoly]
      linear_combination root-(43/500)*normal
    rw [identity]
    exact mul_nonneg den.le (by linarith only [Zhi])
  let a₀ := -(43/500)*r^2+(7/20)*r*t+r-457/500
  let a₁ := -(7/10)*r^2+(13/10)*r*t
  let a₂ := -(193/250)*r^2-(7/10)*r*t+2*r-457/250
  let a₃ := (7/10)*r^2+(27/10)*r*t
  let a₄ := -(1043/500)*r^2+(7/20)*r*t+r-457/500
  have polynomial (x : ℝ) : wallNumerator r t x =
      a₀+a₁*x+a₂*x^2+a₃*x^3+a₄*x^4 := by
    dsimp [wallNumerator,markerNumerator,leftPoly,rightPoly,a₀,a₁,a₂,a₃,a₄]
    ring
  have rt : r*t ≤ r^2/2 := by
    have product := mul_nonneg hr.le (sub_nonneg.mpr ratio)
    nlinarith only [product,sq_nonneg r]
  have a₃pos : 0 ≤ a₃ := by dsimp [a₃]; positivity
  have a₄neg : a₄ ≤ 0 := by
    have lower := mul_nonneg (sub_nonneg.mpr large)
      (show 0 ≤ r+457/500 by linarith only [hr])
    dsimp [a₄]
    nlinarith only [lower,rt,rone]
  have curve : a₂+(2/5)*a₃ ≤ 0 := by
    dsimp [a₂,a₃]
    nlinarith only [rt,sq_nonneg (r-1),rone]
  rw [polynomial] at start endpoint ⊢
  norm_num only [mul_zero,zero_pow,add_zero] at start
  exact quartic_chord a₀ a₁ a₂ a₃ a₄ z Z hz zZ.le Zpos Zhi
    a₃pos a₄neg curve start endpoint

/-- One of the two actual wall support bounds contradicts the surviving
longitudinal separator. The sole wall inequality is derived from its
marker, full container, side>1, and the central half-angle crossing. -/
theorem margins (c s r t z : ℝ) (hr : 0 < r) (ht : 0 ≤ t)
    (normalW : r^2+t^2=1) (hz : 0 ≤ z) (zhi : z ≤ 1/5)
    (angle : (1+c)*z=s) (unitAngle : s*z=1-c)
    (wall : r*t*z < 1-r-(43/500)*t^2) :
    0 ≤ c*r+s*t-(543/500)*r+(7/20)*(c-s)*(c*t-s*r) ∨
    0 ≤ r*(c*r+s*t-(543/500)*r+(7/20)*(c-s)*(c*t-s*r))+r-457/500 := by
  have positive : 0 < 1+z^2 := by positivity
  have cosine : (1+z^2)*c=1-z^2 := by
    linear_combination z*angle+unitAngle
  have sine : (1+z^2)*s=2*z := by
    linear_combination -angle+z*unitAngle
  have cexpr : c=(1-z^2)/(1+z^2) := by
    apply (eq_div_iff (ne_of_gt positive)).mpr
    linarith only [cosine]
  have sexpr : s=2*z/(1+z^2) := by
    apply (eq_div_iff (ne_of_gt positive)).mpr
    linarith only [sine]
  let f := c*r+s*t-(543/500)*r+(7/20)*(c-s)*(c*t-s*r)
  have identity : (1+z^2)^2*f=markerNumerator r t z := by
    dsimp [f,markerNumerator,leftPoly,rightPoly]
    rw [cexpr,sexpr]
    field_simp [ne_of_gt positive]
    ring
  have wallIdentity : (1+z^2)^2*(r*f+r-457/500)=wallNumerator r t z := by
    dsimp [wallNumerator]
    linear_combination r*identity
  have scale : 0 < (1+z^2)^2 := sq_pos_of_pos positive
  by_cases small : r ≤ 457/500
  · have bound := small_cosine r t z hr ht normalW small hz zhi
    left
    change 0 ≤ f
    nlinarith only [identity,bound,scale]
  · have bound := large_cosine r t z hr ht normalW (lt_of_not_ge small).le hz wall
    right
    change 0 ≤ r*f+r-457/500
    nlinarith only [wallIdentity,bound,scale]

#print axioms margins
end N12Compact.MergedWallLongitudinalMargin
