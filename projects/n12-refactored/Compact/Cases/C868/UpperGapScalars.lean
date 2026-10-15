import Compact.Cases.C868.UpperGapPolynomials

/-! Exact C868 upper-sector scalar margins. The only restriction in
`first` and `third` is the actual merged-upper-square tilt 9c≤35s; the two
shallow-lower variants retain 13t≤C. No relation between two different
physical square frames is added. Source only; not yet compiled. -/
namespace N12Compact.C868.UpperGapScalars
open C977CornerCubic
set_option Elab.async false
noncomputable section

private def firstA (c s : ℝ) : ℝ := c-2+(61/100)*c*s+(13/20)*s^2
private def firstB (c s : ℝ) : ℝ := -s-33/50+(61/100)*c^2+(13/20)*c*s
private def secondA (c s : ℝ) : ℝ := c+s-2-(13/25)*c*s
private def secondB (c s : ℝ) : ℝ := c-s-2/5-(13/50)*(c^2-s^2)

private theorem first_disk (c s : ℝ) (h : Normal c s) (tilt : 9*c≤35*s) :
    (firstA c s)^2+(firstB c s)^2≤1 := by
  let x := C1092WallProfileScalars.half c s
  have b := normal_bounds h
  have data := C1092WallProfileScalars.quarter_data c s
    (by linarith only [b.1]) h.1 h.2.2
  have den : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have cf : c=(1-x^2)/(1+x^2) := by
    apply (eq_div_iff den.ne').mpr
    have value := data.2.2.2.1
    change (1+x^2)*c=1-x^2 at value
    linarith only [value]
  have sf : s=2*x/(1+x^2) := by
    apply (eq_div_iff den.ne').mpr
    have value := data.2.2.2.2
    change (1+x^2)*s=2*x at value
    linarith only [value]
  have identity : (1+x^2)^4*(1-(firstA c s)^2-(firstB c s)^2)=
      firstPolynomial x/10000 := by
    dsimp only [firstA,firstB,firstPolynomial]
    rw [cf,sf]
    field_simp [den.ne']
    ring
  have positive : 0≤(1+x^2)^4*(1-(firstA c s)^2-(firstB c s)^2) := by
    rw [identity]
    exact div_nonneg (first_polynomial x (half_lower_of_tilt h tilt) (half_upper h).2)
      (by norm_num)
  have disk := nonneg_of_mul_nonneg_right positive (pow_pos den 4)
  linarith only [disk]

private theorem second_disk (c s : ℝ) (h : Normal c s)
    (low : 1/8≤C1092WallProfileScalars.half c s) :
    (secondA c s)^2+(secondB c s)^2≤1 := by
  let x := C1092WallProfileScalars.half c s
  have b := normal_bounds h
  have data := C1092WallProfileScalars.quarter_data c s
    (by linarith only [b.1]) h.1 h.2.2
  have den : 0<1+x^2 := by nlinarith only [sq_nonneg x]
  have cf : c=(1-x^2)/(1+x^2) := by
    apply (eq_div_iff den.ne').mpr
    have value := data.2.2.2.1
    change (1+x^2)*c=1-x^2 at value
    linarith only [value]
  have sf : s=2*x/(1+x^2) := by
    apply (eq_div_iff den.ne').mpr
    have value := data.2.2.2.2
    change (1+x^2)*s=2*x at value
    linarith only [value]
  have identity : (1+x^2)^4*(1-(secondA c s)^2-(secondB c s)^2)=
      secondPolynomial x/2500 := by
    dsimp only [secondA,secondB,secondPolynomial]
    rw [cf,sf]
    field_simp [den.ne']
    ring
  have positive : 0≤(1+x^2)^4*(1-(secondA c s)^2-(secondB c s)^2) := by
    rw [identity]
    exact div_nonneg (second_polynomial x low (half_upper h).2) (by norm_num)
  have disk := nonneg_of_mul_nonneg_right positive (pow_pos den 4)
  linarith only [disk]

theorem first (c s C t : ℝ) (h : Normal c s) (a : Normal C t)
    (tilt : 9*c≤35*s) :
    0≤1+C*(c-2+(61/100)*c*s+(13/20)*s^2)+
      t*(-s-33/50+(61/100)*c^2+(13/20)*c*s) :=
  disk_margin _ _ C t a.2.2 (first_disk c s h tilt)

theorem second (c s C t : ℝ) (h : Normal c s) (a : Normal C t) :
    0≤1+C*(c+s-2-(13/25)*c*s)+
      t*(c-s-2/5-(13/50)*(c^2-s^2)) := by
  by_cases low : 1/8≤C1092WallProfileScalars.half c s
  · exact disk_margin _ _ C t a.2.2 (second_disk c s h low)
  · have b := normal_bounds h
    have e := normal_bounds a
    have cn : 0≤c := by linarith only [b.1]
    have Cn : 0≤C := by linarith only [e.1]
    have cs := mul_nonneg cn h.1
    have arc := circle_arc h
    have data := C1092WallProfileScalars.quarter_data c s cn h.1 h.2.2
    have weighted := mul_nonneg (show 0≤1+c by linarith only [cn])
      (show 0≤1/8-C1092WallProfileScalars.half c s by linarith only [low])
    have sine : s≤1/4 := by nlinarith only [weighted,data.2.2.1,b.2.1]
    have cosine : 24/25≤c := by
      apply le_of_not_gt
      intro bad
      have product := mul_nonneg (show 0≤24/25-c by linarith only [bad])
        (show 0≤24/25+c by linarith only [cn])
      have power := pow_le_pow_left₀ h.1 sine 2
      norm_num at power
      nlinarith only [product,power,h.2.2]
    have firstBound : 0≤1+secondA c s := by
      dsimp only [secondA]
      linarith only [arc,cs]
    have lastBound : 0≤secondB c s := by
      dsimp only [secondB]
      nlinarith only [cosine,sine,h.2.2,sq_nonneg s]
    have firstTerm := mul_nonneg Cn firstBound
    have lastTerm := mul_nonneg a.1 lastBound
    dsimp only [secondA,secondB] at firstTerm lastTerm
    linarith only [firstTerm,lastTerm,e.2.1]

/-- The shallow-lower first variant. The side-one constant has been
absorbed into C, retaining exactly the actual 13t≤C hypothesis. -/
theorem third (c s C t : ℝ) (h : Normal c s) (a : Normal C t)
    (tilt : 9*c≤35*s) (shallow : 13*t≤C) :
    0≤C*(c-1+(61/100)*c*s+(13/20)*s^2)+
      t*(-s-13/25+(61/100)*c^2+(13/20)*c*s) := by
  let A := c-1+(61/100)*c*s+(13/20)*s^2
  let B := -s-13/25+(61/100)*c^2+(13/20)*c*s
  have b := normal_bounds h
  have cn : 0≤c := by linarith only [b.1]
  have cs := mul_nonneg cn h.1
  have reserve := mul_nonneg (show 0≤1-c by linarith only [b.2.1])
    (show 0≤(13/20)*(1+c)-1 by linarith only [b.1])
  have base : 0≤c-1+(13/20)*s^2 := by
    nlinarith only [reserve,h.2.2]
  have An : 0≤A := by dsimp only [A]; linarith only [base,cs]
  have cosineWeight := mul_nonneg h.1 (show 0≤c-7/10 by linarith only [b.1])
  have aFloor : (427/1000)*s≤A := by
    dsimp only [A]
    nlinarith only [base,cosineWeight]
  have bFloor : -s-13/25≤B := by
    dsimp only [B]
    nlinarith only [cs,sq_nonneg c]
  have sine : 9/50≤s := by linarith only [tilt,b.1]
  have together : 0≤13*A+B := by linarith only [aFloor,bFloor,sine]
  have firstTerm := mul_nonneg (show 0≤C-13*t by linarith only [shallow]) An
  have lastTerm := mul_nonneg a.1 together
  change 0≤C*A+t*B
  nlinarith only [firstTerm,lastTerm]

/-- The shallow-lower second variant needs no merged-upper-square tilt. -/
theorem fourth (c s C t : ℝ) (h : Normal c s) (a : Normal C t)
    (shallow : 13*t≤C) :
    0≤C*(c+s-1-(13/25)*c*s)+
      t*(c-s-(13/50)*(c^2-s^2)-13/50) := by
  let A := c+s-1-(13/25)*c*s
  let B := c-s-(13/50)*(c^2-s^2)-13/50
  have b := normal_bounds h
  have arc := circle_arc h
  have cosineWeight := mul_nonneg h.1 (show 0≤c-7/10 by linarith only [b.1])
  have aFloor : (49/250)*s≤A := by
    dsimp only [A]
    nlinarith only [arc,cosineWeight]
  have An : 0≤A := by linarith only [aFloor,h.1]
  have bFloor : 9/50-s≤B := by
    dsimp only [B]
    nlinarith only [b.1,h.2.2,sq_nonneg s]
  have together : 0≤13*A+B := by linarith only [aFloor,bFloor,h.1]
  have firstTerm := mul_nonneg (show 0≤C-13*t by linarith only [shallow]) An
  have lastTerm := mul_nonneg a.1 together
  change 0≤C*A+t*B
  nlinarith only [firstTerm,lastTerm]

end
#print axioms first
#print axioms second
#print axioms third
#print axioms fourth
end N12Compact.C868.UpperGapScalars
