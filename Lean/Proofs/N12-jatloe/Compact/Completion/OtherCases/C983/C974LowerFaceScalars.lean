import Compact.Completion.C981.SupportForms

/-! Scalar identities in §2 of `C974-THREE-SQUARE-ENDING.md`.
This is a direct source translation of the written continuous comparisons.
No compiler replay or numerical computation has been performed. -/
namespace N12Compact.Completion.OtherCases.C983.C974LowerFace
set_option Elab.async false
noncomputable section

/-- Positive canonical frames with the manuscript's strict 3/4 slope bound. -/
theorem half_data (c s : ℝ) (cp : 0<c) (sp : 0<s)
    (unit : c^2+s^2=1) (slope : 4*s<3*c) :
    let x := s/(1+c)
    0<x ∧ x<1/3 ∧ s*x=1-c ∧
      c=(1-x^2)/(1+x^2) ∧ s=2*x/(1+x^2) := by
  let x := s/(1+c)
  have denominator : 0<1+c := by linarith only [cp]
  have xp : 0<x := div_pos sp denominator
  have relation : x*(1+c)=s := div_mul_cancel₀ _ denominator.ne'
  have small : 3*s<1+c := by
    by_contra no
    have lower : 1+c≤3*s := le_of_not_gt no
    have large : 4/5<c := by linarith only [slope,lower]
    have product := mul_nonneg (show 0≤3*s-(1+c) by linarith only [lower])
      (show 0≤3*s+(1+c) by linarith only [sp,cp])
    nlinarith only [unit,product,large]
  have xt : x<1/3 := (div_lt_iff₀ denominator).mpr (by linarith only [small])
  have half : s*x=1-c := by
    apply (mul_right_cancel₀ denominator.ne')
    linear_combination s*relation+unit
  have sForm : s=2*x/(1+x^2) := by
    apply (eq_div_iff (by positivity : (1+x^2:ℝ)≠0)).mpr
    linear_combination x*half-relation
  have cForm : c=(1-x^2)/(1+x^2) := by
    apply (eq_div_iff (by positivity : (1+x^2:ℝ)≠0)).mpr
    linear_combination x*relation+half
  exact ⟨xp,xt,half,cForm,sForm⟩

/-- The weaker rational cosine bound recorded in manuscript (5). -/
theorem cosine_lower (d t : ℝ) (dp : 0<d) (tp : 0<t)
    (unit : d^2+t^2=1) (slope : 3*t<2*d) : 83/100<d := by
  have product := mul_pos (sub_pos.mpr slope)
    (show 0<2*d+3*t by linarith only [dp,tp])
  nlinarith only [unit,product,dp]

private theorem denominator_pos (x z : ℝ) : 0<(1+x^2)*(1+z^2) := by positivity

/-- The sign of the relative angle is exactly the sign of x-z. -/
theorem sigma_identity (l h d t x z : ℝ)
    (lc : l=(1-x^2)/(1+x^2)) (hs : h=2*x/(1+x^2))
    (dc : d=(1-z^2)/(1+z^2)) (ts : t=2*z/(1+z^2)) :
    (h*d-l*t)*((1+x^2)*(1+z^2))=2*(x-z)*(1+x*z) := by
  rw [lc,hs,dc,ts]
  field_simp
  <;> ring

theorem sine_identity (l h d t x z : ℝ)
    (hs : h=2*x/(1+x^2)) (ts : t=2*z/(1+z^2)) :
    (h-t)*((1+x^2)*(1+z^2))=2*(x-z)*(1-x*z) := by
  rw [hs,ts]
  field_simp
  <;> ring

/-- §2.1: the W-owned separator when x is at least z. -/
theorem forward_w_large (l h d t x z : ℝ)
    (dp : 0<d) (hn : 0<h) (tn : 0<t) (hSmall : h<1) (tSmall : t<1)
    (xp : 0<x) (zp : 0<z) (xt : x<1/3) (zt : z<1/3) (order : z≤x)
    (hx : h*x=1-l) (tz : t*z=1-d)
    (xRelation : x*(1+l)=h) (zRelation : z*(1+d)=t)
    (hs : h=2*x/(1+x^2)) (ts : t=2*z/(1+z^2)) :
    -z*(1-t)≤(l*d+h*t)*(1-x)+(h*d-l*t)-d := by
  have denominator := denominator_pos x z
  have product : x*z<1 := by
    have a := mul_pos xp (show 0<1/3-z by linarith only [zt])
    nlinarith only [a,xt]
  have sinOrder : t≤h := by
    have identity := sine_identity l h d t x z hs ts
    have nonnegative := mul_nonneg (sub_nonneg.mpr order)
      (show 0≤1-x*z by linarith only [product])
    have scaled : 0≤(h-t)*((1+x^2)*(1+z^2)) := by
      rw [identity]
      linarith only [nonnegative]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right denominator).mp scaled)
  have dz : d*z-t= -z := by
    nlinarith only [zRelation]
  have identity : (l*d+h*t)*(1-x)+(h*d-l*t)-d=(1-h)*(d*x-t) := by
    linear_combination (d-t)*hx-d*xRelation
  rw [identity]
  rcases le_total 0 (d*x-t) with positive | negative
  · have nonnegative := mul_nonneg (show 0≤1-h by linarith only [hSmall]) positive
    have kPositive := mul_pos zp (show 0<1-t by linarith only [tSmall])
    linarith only [nonnegative,kPositive]
  · have first := mul_nonneg (sub_nonneg.mpr sinOrder) (neg_nonneg.mpr negative)
    have second := mul_nonneg (show 0≤1-t by linarith only [tSmall])
      (mul_nonneg dp.le (sub_nonneg.mpr order))
    have dzWeight : (1-t)*(d*z-t)= -(1-t)*z := by rw [dz]; ring
    nlinarith only [first,second,dzWeight]

private def P (x z : ℝ) := x^2*(1+z^2)^2+
  x*(-z^3-6*z^2+z-2)-z^4+2*z^3-3*z^2-2*z

/-- The elementary bounds immediately following manuscript (9). -/
private theorem p_negative (x z : ℝ) (xp : 0<x) (zp : 0<z)
    (xt : x<1/3) (zt : z<1/3) : P x z<0 := by
  have z2 : z^2≤1/9 := by
    calc
      z^2≤(1/3:ℝ)^2 := by gcongr
      _=1/9 := by norm_num
  have factor : (1+z^2)^2≤4/3 := by
    have p := mul_nonneg (show 0≤1/9-z^2 by linarith only [z2])
      (show 0≤10/9+(1+z^2) by positivity)
    nlinarith only [p]
  have xx : x^2≤x/3 := by nlinarith only [mul_nonneg xp.le (sub_nonneg.mpr xt.le)]
  have first : x^2*(1+z^2)^2≤4*x/9 := by
    have a := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr factor)
    nlinarith only [a,xx]
  have cube : 0≤z^3 := by positivity
  have coefficient : -z^3-6*z^2+z-2≤ -5/3 := by
    nlinarith only [cube,sq_nonneg z,zt]
  have middle := mul_nonneg xp.le (show 0≤ -5/3-(-z^3-6*z^2+z-2) by
    linarith only [coefficient])
  have last := mul_nonneg (sq_nonneg z) (show 0≤(z-1)^2+2 by positivity)
  dsimp only [P]
  nlinarith only [first,middle,last,xp,zp]

/-- §2.2, exact identity (9) and its nonnegative sign. -/
theorem forward_k_large (l h d t x z : ℝ)
    (xp : 0<x) (zp : 0<z) (xt : x<1/3) (zt : z<1/3) (order : z≤x)
    (lc : l=(1-x^2)/(1+x^2)) (hs : h=2*x/(1+x^2))
    (dc : d=(1-z^2)/(1+z^2)) (ts : t=2*z/(1+z^2)) :
    0≤(l*d+h*t)*z*(1-t)+(h*d-l*t)*(1-d/2)-x*(1-h) := by
  have identity : ((l*d+h*t)*z*(1-t)+(h*d-l*t)*(1-d/2)-x*(1-h))*
      ((1+x^2)*(1+z^2)^2)= -(x-z)*P x z := by
    rw [lc,hs,dc,ts]
    dsimp only [P]
    field_simp
    <;> ring
  have sign := mul_nonneg (sub_nonneg.mpr order) (neg_nonneg.mpr (p_negative x z xp zp xt zt).le)
  have denominator : 0<(1+x^2)*(1+z^2)^2 := by positivity
  apply (mul_nonneg_iff_of_pos_right denominator).mp
  rw [identity]
  nlinarith only [sign]

private def Q (x z : ℝ) := x^2*(z^2-1)+2*x*(z+1)+(1-z)^2

/-- §2.3, exact identity (10) and its strict sign. -/
theorem forward_w_small (l h d t x z : ℝ)
    (xp : 0<x) (zp : 0<z) (xt : x<1/3) (order : x<z)
    (lc : l=(1-x^2)/(1+x^2)) (hs : h=2*x/(1+x^2))
    (dc : d=(1-z^2)/(1+z^2)) (ts : t=2*z/(1+z^2)) :
    0<(l*d+h*t)*(1-x)-d+z*(1-t) := by
  have qPositive : 0<Q x z := by
    have leading := mul_pos xp (show 0<2-x by linarith only [xt])
    have rest := mul_nonneg (sq_nonneg x) (sq_nonneg z)
    have cross := mul_pos xp zp
    dsimp only [Q]
    nlinarith only [leading,rest,cross,sq_nonneg (1-z)]
  have identity : ((l*d+h*t)*(1-x)-d+z*(1-t))*
      ((1+x^2)*(1+z^2))= -(x-z)*Q x z := by
    rw [lc,hs,dc,ts]
    dsimp only [Q]
    field_simp
    <;> ring
  have positive := mul_pos (sub_pos.mpr order) qPositive
  have denominator := denominator_pos x z
  apply (mul_pos_iff_of_pos_right denominator).mp
  rw [identity]
  nlinarith only [positive]

private def R (x z : ℝ) := x^2*(1+z^2)^2+
  2*x*(z^3-3*z^2+z-1)-z^4+2*z^3-2*z+1

/-- The polynomial derivative estimate and the endpoint cubic in (13).
An exact secant factorization expresses the same decreasing quadratic. -/
private theorem r_positive (x z : ℝ) (xp : 0<x) (zp : 0<z)
    (order : x<z) (zt : z≤2/7) : 0<R x z := by
  have third : z<1/3 := by linarith only [zt]
  have xt : x<1/3 := lt_trans order third
  have z2 : z^2≤1/9 := by
    calc
      z^2≤(1/3:ℝ)^2 := by gcongr
      _=1/9 := by norm_num
  have z3 : z^3≤1/27 := by
    calc
      z^3≤(1/3:ℝ)^3 := by gcongr
      _=1/27 := by norm_num
  have factor : (1+z^2)^2≤100/81 := by
    calc
      (1+z^2)^2≤(1+1/9:ℝ)^2 := by gcongr
      _=100/81 := by norm_num
  have leading : (x+z)*(1+z^2)^2≤200/243 := by
    calc
      (x+z)*(1+z^2)^2≤(2/3:ℝ)*(100/81) := by gcongr <;> linarith
      _=200/243 := by norm_num
  have derivative : (x+z)*(1+z^2)^2+2*(z^3-3*z^2+z-1)<0 := by
    nlinarith only [leading,z3,third,sq_nonneg z]
  have difference : R x z-R z z=
      (x-z)*((x+z)*(1+z^2)^2+2*(z^3-3*z^2+z-1)) := by dsimp only [R]; ring
  have decreasing := mul_pos_of_neg_of_neg (sub_neg.mpr order) derivative
  have z2sharp : z^2≤4/49 := by
    calc
      z^2≤(2/7:ℝ)^2 := by gcongr
      _=4/49 := by norm_num
  have z3sharp : z^3≤8/343 := by
    calc
      z^3≤(2/7:ℝ)^3 := by gcongr
      _=8/343 := by norm_num
  have cubic : 0<1-3*z-z^2-z^3 := by linarith only [zt,z2sharp,z3sharp]
  have endpoint : R z z=(1-z)*(1+z^2)*(1-3*z-z^2-z^3) := by dsimp only [R]; ring
  have positive := mul_pos (mul_pos (show 0<1-z by linarith only [third])
    (show 0<1+z^2 by positivity)) cubic
  nlinarith only [difference,decreasing,endpoint,positive]

/-- §2.4 for z≤2/7: exact identity (12), with its strict sign. -/
theorem forward_k_small (l h d t x z : ℝ)
    (xp : 0<x) (zp : 0<z) (order : x<z) (zt : z≤2/7)
    (lc : l=(1-x^2)/(1+x^2)) (hs : h=2*x/(1+x^2))
    (dc : d=(1-z^2)/(1+z^2)) (ts : t=2*z/(1+z^2)) :
    0<(l*d+h*t)*z*(1-t)-x*(1-h) := by
  have identity : ((l*d+h*t)*z*(1-t)-x*(1-h))*
      ((1+x^2)*(1+z^2)^2)= -(x-z)*R x z := by
    rw [lc,hs,dc,ts]
    dsimp only [R]
    field_simp
    <;> ring
  have positive := mul_pos (sub_pos.mpr order) (r_positive x z xp zp order zt)
  have denominator : 0<(1+x^2)*(1+z^2)^2 := by positivity
  apply (mul_pos_iff_of_pos_right denominator).mp
  rw [identity]
  nlinarith only [positive]

end
end N12Compact.Completion.OtherCases.C983.C974LowerFace
