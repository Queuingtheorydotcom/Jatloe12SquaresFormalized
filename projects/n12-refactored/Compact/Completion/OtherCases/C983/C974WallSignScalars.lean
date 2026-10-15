import Compact.Completion.OtherCases.C983.C974SingletonSign

/-! The continuous rectangle estimate (12)--(13) in
MISSING-CORNER-WALL-SIGN §1.6. These are the manuscript's explicit
polynomial comparisons, not a generated or sampled certificate. -/
namespace N12Compact.Completion.OtherCases.C983.C974MissingCorner
set_option Elab.async false
noncomputable section

theorem quadrant_half (l h : ℝ) (lp : 0<l) (hp : 0<h) (unit : l^2+h^2=1) :
    let x := h/(1+l)
    0<x ∧ h*x=1-l ∧ l=(1-x^2)/(1+x^2) ∧ h=2*x/(1+x^2) := by
  let x := h/(1+l)
  have denominator : 0<1+l := by positivity
  have relation : x*(1+l)=h := div_mul_cancel₀ _ denominator.ne'
  have half : h*x=1-l := by
    apply (mul_right_cancel₀ denominator.ne')
    linear_combination h*relation+unit
  have first : l=(1-x^2)/(1+x^2) := by
    apply (eq_div_iff (by positivity : (1+x^2:ℝ)≠0)).mpr
    linear_combination x*relation+half
  have last : h=2*x/(1+x^2) := by
    apply (eq_div_iff (by positivity : (1+x^2:ℝ)≠0)).mpr
    linear_combination x*half-relation
  exact ⟨div_pos hp denominator,half,first,last⟩

private def wallPolynomial (x y : ℝ) := x^2*(2-x)+y*(1-4*x-x^2)+
  y^2*(-2*x^3+6*x^2-2)+y^3*(-3*x^2-4*x+3)+y^4*(-x^3+4*x^2-4*x-2)

private theorem wallPolynomial_pos (x y : ℝ) (xp : 0<x) (xu : x≤2/3)
    (yn : 0≤y) (yu : y≤1/7) : 0<wallPolynomial x y := by
  have x2 : x^2≤4/9 := by
    calc
      x^2≤(2/3:ℝ)^2 := by gcongr
      _=4/9 := by norm_num
  have x3 : x^3≤8/27 := by
    calc
      x^3≤(2/3:ℝ)^3 := by gcongr
      _=8/27 := by norm_num
  have c2 : -2≤ -2*x^3+6*x^2-2 := by
    nlinarith only [mul_nonneg (sq_nonneg x) (show 0≤6-2*x by linarith only [xu])]
  have c3 : -1≤ -3*x^2-4*x+3 := by linarith only [x2,xu]
  have c4 : -5≤ -x^3+4*x^2-4*x-2 := by nlinarith only [x3,xu,sq_nonneg x]
  have y2 : y^2≤y/7 := by nlinarith only [mul_nonneg yn (sub_nonneg.mpr yu)]
  have y3 : y^3≤y/49 := by
    have first := mul_nonneg yn (sub_nonneg.mpr y2)
    nlinarith only [first,y2]
  have y4 : y^4≤y/343 := by
    have first := mul_nonneg yn (sub_nonneg.mpr y3)
    nlinarith only [first,y2]
  have tail : 2*y^2+y^3+5*y^4≤y/3 := by linarith only [y2,y3,y4,yn]
  have w2 := mul_nonneg (sq_nonneg y) (show 0≤(-2*x^3+6*x^2-2)+2 by linarith only [c2])
  have w3 := mul_nonneg (show 0≤y^3 by positivity) (show 0≤(-3*x^2-4*x+3)+1 by linarith only [c3])
  have w4 := mul_nonneg (show 0≤y^4 by positivity) (show 0≤(-x^3+4*x^2-4*x-2)+5 by linarith only [c4])
  have lower : x^2*(2-x)+y*(1-4*x-x^2)-y/3≤wallPolynomial x y := by
    dsimp only [wallPolynomial]
    nlinarith only [w2,w3,w4,tail]
  have leading := mul_nonneg (sq_nonneg x)
    (show 0≤2-x-y-25/21 by linarith only [xu,yu])
  have middle : (25/21)*x^2-4*x*y+(2/3)*y≤wallPolynomial x y := by
    nlinarith only [lower,leading]
  have last := mul_nonneg yn (sub_nonneg.mpr yu)
  have complete : (25/21)*(x-42*y/25)^2+(14/75)*y≤wallPolynomial x y := by
    nlinarith only [middle,last]
  rcases yn.eq_or_lt with zero | positive
  · have yz : y=0 := zero.symm
    rw [yz]
    dsimp only [wallPolynomial]
    simpa using mul_pos (sq_pos_of_pos xp) (show 0<2-x by linarith only [xu])
  · nlinarith only [complete,sq_nonneg (x-42*y/25),positive]

theorem negative_wall_scalar (l h d t x y : ℝ)
    (xp : 0<x) (xu : x≤2/3) (yn : 0≤y) (yu : y≤1/7)
    (lc : l=(1-x^2)/(1+x^2)) (hs : h=2*x/(1+x^2))
    (dc : d=(1-y^2)/(1+y^2)) (ts : t=2*y/(1+y^2)) :
    0<1-l-x+(l*d-h*t)*(1-d)+(l*t+h*d)*(1-t-d/2) := by
  have identity : (1-l-x+(l*d-h*t)*(1-d)+(l*t+h*d)*(1-t-d/2))*
      ((1+x^2)*(1+y^2)^2)=wallPolynomial x y := by
    rw [lc,hs,dc,ts]
    dsimp only [wallPolynomial]
    field_simp
    <;> ring
  have denominator : 0<(1+x^2)*(1+y^2)^2 := by positivity
  apply (mul_pos_iff_of_pos_right denominator).mp
  rw [identity]
  exact wallPolynomial_pos x y xp xu yn yu

end
#print axioms negative_wall_scalar
end N12Compact.Completion.OtherCases.C983.C974MissingCorner
