import Compact.Completion.C981.HalfAngle
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Positivity

/-! The large-half-angle exclusion in C974-THREE-SQUARE-ENDING, §2.4,
equations (14)--(17). The small-x estimate uses the displayed derivative.
For large x, the manuscript's bound on the difference of the two angles
is written as the equivalent rational inequality 46 γ < 9 κ. All constants
are exact. Source translation only; this module has not been compiled. -/
namespace N12Compact.Completion.OtherCases.C983.C974LowerFace
open Set
set_option Elab.async false
noncomputable section

private def f (x : ℝ) : ℝ := x*(1-x)^2/(1+x^2)

private theorem f_derivative (x : ℝ) :
    HasDerivAt f ((1-x)*(1-3*x-x^2-x^3)/(1+x^2)^2) x := by
  have denominator : 1+x^2≠0 := ne_of_gt (by positivity)
  have result := ((hasDerivAt_id x).mul
    (((hasDerivAt_id x).const_sub 1).pow 2)).div
      (((hasDerivAt_id x).pow 2).const_add 1) denominator
  convert result using 1 <;> dsimp only [f] <;> ring

private theorem f_small (x : ℝ) (low : 0≤x) (high : x≤1/5) :
    f x≤8/65 := by
  have increasing : MonotoneOn f (Icc 0 (1/5)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro q _
      exact (f_derivative q).continuousAt.continuousWithinAt
    · intro q _
      exact (f_derivative q).differentiableAt.differentiableWithinAt
    · intro q hq
      have interval := interior_subset hq
      have qnonneg : 0≤q := interval.1
      have first : 0≤1-q := by linarith only [interval.2]
      have quadratic := mul_nonneg
        (show 0≤1/5-q by linarith only [interval.2])
        (show 0≤1/5+q by linarith only [interval.1])
      have cubic := mul_nonneg
        (show 0≤1/5-q by linarith only [interval.2])
        (show 0≤q^2+q/5+1/25 by positivity)
      have second : 0≤1-3*q-q^2-q^3 := by
        nlinarith only [interval.2,quadratic,cubic]
      rw [(f_derivative q).deriv]
      exact div_nonneg (mul_nonneg first second) (sq_nonneg _)
  have bound := increasing ⟨low,high⟩ (show (1/5 : ℝ)∈Icc 0 (1/5) by
    constructor <;> norm_num) high
  have endpoint : f (1/5)=8/65 := by norm_num [f]
  rwa [endpoint] at bound

/-- The completed-square numerator in equation (16). -/
private theorem f_uniform (x : ℝ) (high : x≤1/3) : f x<7/50 := by
  have cubic := mul_nonneg (sq_nonneg x)
    (show 0≤1/3-x by linarith only [high])
  have numerator : 0<7-50*x+107*x^2-50*x^3 := by
    nlinarith only [cubic,sq_nonneg (x-75/271)]
  dsimp only [f]
  apply (div_lt_iff₀ (show 0<1+x^2 by positivity)).mpr
  nlinarith only [numerator]

/-- Rational form of the written angle-difference bound
`atan(2/3)-2 atan(1/5)`: its tangent is 9/46. -/
private theorem large_x_dot (l h d t x z : ℝ)
    (lp : 0<l) (hp : 0<h) (dp : 0<d) (tp : 0<t)
    (lunit : l^2+h^2=1) (dunit : d^2+t^2=1) (order : h≤l)
    (xlow : 1/5≤x) (xz : x<z)
    (lform : l=(1-x^2)/(1+x^2)) (hform : h=2*x/(1+x^2))
    (dform : d=(1-z^2)/(1+z^2)) (tform : t=2*z/(1+z^2))
    (slope : 3*t<2*d) : 49/50<l*d+h*t := by
  let κ := l*d+h*t
  let γ := l*t-h*d
  have xp : 0<x := by linarith only [xlow]
  have zp : 0<z := lt_trans xp xz
  have xd : 0<1+x^2 := by positivity
  have zd : 0<1+z^2 := by positivity
  have kp : 0<κ := by dsimp only [κ]; positivity
  have gamma_identity : γ=2*(z-x)*(1+x*z)/((1+x^2)*(1+z^2)) := by
    dsimp only [γ]
    rw [lform,hform,dform,tform]
    field_simp [xd.ne',zd.ne']
    ring
  have gp : 0<γ := by
    rw [gamma_identity]
    exact div_pos (mul_pos (mul_pos (by norm_num) (sub_pos.mpr xz))
      (by positivity)) (mul_pos xd zd)
  have singleton_identity : 12*h-5*l=(5*x-1)*(x+5)/(1+x^2) := by
    rw [hform,lform]
    field_simp [xd.ne']
    ring
  have singleton : 0≤12*h-5*l := by
    rw [singleton_identity]
    exact div_nonneg (mul_nonneg (by linarith only [xlow])
      (by linarith only [xp])) xd.le
  have coefficient : 0<46*l-9*h := by linarith only [lp,order]
  have first := mul_pos (div_pos coefficient (by norm_num))
    (show 0<2*d-3*t by linarith only [slope])
  have second := mul_nonneg (show 0≤13*d/3 by positivity) singleton
  have angle_identity : 9*κ-46*γ=
      ((46*l-9*h)/3)*(2*d-3*t)+(13*d/3)*(12*h-5*l) := by
    dsimp only [κ,γ]
    ring
  have angle : 46*γ<9*κ := by linarith only [first,second,angle_identity]
  have squared := mul_pos (show 0<9*κ-46*γ by linarith only [angle])
    (show 0<9*κ+46*γ by linarith only [kp,gp])
  have circle : κ^2+γ^2=1 := by
    dsimp only [κ,γ]
    calc
      (l*d+h*t)^2+(l*t-h*d)^2=(l^2+h^2)*(d^2+t^2) := by ring
      _ = 1 := by rw [lunit,dunit]; ring
  -- This is the manuscript's exact comparison
  -- 46²·50² - 49²·13³ = 15003 > 0, with 13³ = 46²+9².
  have dot_square : (49/50)^2<κ^2 := by nlinarith only [squared,circle]
  change 49/50<κ
  apply lt_of_not_ge
  intro bad
  have impossible := mul_nonneg (sub_nonneg.mpr bad)
    (show 0≤49/50+κ by linarith only [kp])
  nlinarith only [dot_square,impossible]

/-- Equations (15) and (17) contradict the necessary separating-direction
inequality (14), throughout the large-z interval. The half-angle formulas
and angle bounds are exactly those supplied before §2.4. -/
theorem large_half (l h d t x z : ℝ)
    (lp : 0<l) (hp : 0<h) (dp : 0<d) (tp : 0<t)
    (lunit : l^2+h^2=1) (dunit : d^2+t^2=1) (order : h≤l)
    (xp : 0<x) (xz : x<z) (zhigh : z<1/3) (zlow : 2/7≤z)
    (lform : l=(1-x^2)/(1+x^2)) (hform : h=2*x/(1+x^2))
    (dform : d=(1-z^2)/(1+z^2)) (tform : t=2*z/(1+z^2))
    (dlow : 83/100<d) (slope : 3*t<2*d) :
    x*(1-h)<(l*d+h*t)*(1-d) := by
  have xd : 0<1+x^2 := by positivity
  have zd : 0<1+z^2 := by positivity
  have zp : 0<z := lt_trans xp xz
  have xhigh : x<1/3 := lt_trans xz zhigh
  have dsquare := mul_nonneg
    (show 0≤z-2/7 by linarith only [zlow])
    (show 0≤z+2/7 by linarith only [zp])
  have dhigh : d≤45/53 := by
    rw [dform]
    apply (div_le_iff₀ zd).mpr
    nlinarith only [dsquare]
  have gap : 8/53≤1-d := by linarith only [dhigh]
  have kp : 0<l*d+h*t := by positivity
  have f_identity : x*(1-h)=f x := by
    rw [hform]
    dsimp only [f]
    field_simp [xd.ne']
    ring
  rw [f_identity]
  by_cases small : x≤1/5
  · have fbound := f_small x xp.le small
    have left_identity : l-1= -x*h := by
      rw [lform,hform]
      field_simp [xd.ne']
      ring
    have right_identity : t=z*(1+d) := by
      rw [dform,tform]
      field_simp [zd.ne']
      ring
    have advancing := mul_pos dp (sub_pos.mpr xz)
    have projection : 0<t-d*x := by nlinarith only [right_identity,advancing,zp]
    have dot_identity : l*d+h*t-d=h*(t-d*x) := by
      calc
        l*d+h*t-d=(l-1)*d+h*t := by ring
        _ = (-x*h)*d+h*t := by rw [left_identity]
        _ = h*(t-d*x) := by ring
    have dot_lower : d<l*d+h*t := by
      have positive := mul_pos hp projection
      linarith only [dot_identity,positive]
    have lower := mul_lt_mul_of_pos_right (lt_trans dlow dot_lower)
      (show (0 : ℝ)<8/53 by norm_num)
    have last := mul_le_mul_of_nonneg_left gap kp.le
    -- (83/100)*(8/53)-8/65 = 38/17225 > 0.
    linarith only [fbound,lower,last]
  · have dot_bound := large_x_dot l h d t x z lp hp dp tp lunit dunit order
      (le_of_lt (lt_of_not_ge small)) xz lform hform dform tform slope
    have fbound := f_uniform x xhigh.le
    have lower := mul_lt_mul_of_pos_right dot_bound
      (show (0 : ℝ)<8/53 by norm_num)
    have last := mul_le_mul_of_nonneg_left gap kp.le
    -- (49/50)*(8/53)-7/50 = 21/2650 > 0.
    linarith only [fbound,lower,last]

end
end N12Compact.Completion.OtherCases.C983.C974LowerFace
