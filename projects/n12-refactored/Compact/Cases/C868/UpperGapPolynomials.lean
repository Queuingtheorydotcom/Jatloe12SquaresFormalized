import Compact.Geometry.C977CornerCubic
import Compact.Completion.C1092.WallProfileScalars

/-! Small exact algebra for the two C868 upper-sector margins. The first
norm polynomial has a monotone negative tail. The second lies above one
cubic whose exact endpoint chord is positive. No sampled angles or stored
pose certificates are used. Source only; not yet compiled. -/
namespace N12Compact.C868.UpperGapScalars
open C977CornerCubic
set_option Elab.async false
noncomputable section

def firstPolynomial (x : ℝ) : ℝ :=
  -25+23700*x-10324*x^2-29100*x^3-100598*x^4-
    129300*x^5-170324*x^6-76500*x^7-80025*x^8

def secondPolynomial (x : ℝ) : ℝ :=
  -289+8200*x-23596*x^2+45400*x^3-73214*x^4+
    66200*x^5-76796*x^6+29000*x^7-26889*x^8

theorem first_polynomial (x : ℝ) (low : 1/8≤x) (high : x≤5/12) :
    0≤firstPolynomial x := by
  have xn : 0≤x := by linarith only [low]
  have p2 := pow_le_pow_left₀ xn high 2
  have p3 := pow_le_pow_left₀ xn high 3
  have p4 := pow_le_pow_left₀ xn high 4
  have p5 := pow_le_pow_left₀ xn high 5
  have p6 := pow_le_pow_left₀ xn high 6
  have p7 := pow_le_pow_left₀ xn high 7
  norm_num at p2 p3 p4 p5 p6 p7
  have tail : 400≤23700-10324*x-29100*x^2-100598*x^3-
      129300*x^4-170324*x^5-76500*x^6-80025*x^7 := by
    linarith only [high,p2,p3,p4,p5,p6,p7]
  have product := mul_nonneg xn (sub_nonneg.mpr tail)
  dsimp only [firstPolynomial]
  nlinarith only [product,low]

theorem second_polynomial (x : ℝ) (low : 1/8≤x) (high : x≤5/12) :
    0≤secondPolynomial x := by
  have xn : 0≤x := by linarith only [low]
  let f : ℝ→ℝ := fun z => -289+8200*z-23600*z^2+14800*z^3
  have left : 0≤(5/12-x)*f (1/8) :=
    mul_nonneg (sub_nonneg.mpr high) (by norm_num [f])
  have right : 0≤(x-1/8)*f (5/12) :=
    mul_nonneg (sub_nonneg.mpr low) (by norm_num [f])
  have bend : 0≤(5/12-1/8)*(x-1/8)*(5/12-x)*
      (23600-14800*(x+1/8+5/12)) := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr low))
        (sub_nonneg.mpr high)
    · linarith only [high]
  have chord : (5/12-1/8)*f x =
      (5/12-x)*f (1/8)+(x-1/8)*f (5/12)+
      (5/12-1/8)*(x-1/8)*(5/12-x)*(23600-14800*(x+1/8+5/12)) := by
    dsimp only [f]; ring
  have base : 0≤f x := by linarith only [left,right,bend,chord]
  have r3 := mul_nonneg (pow_nonneg xn 3)
    (show 0≤30600-73214*x by linarith only [high])
  have r5 := mul_nonneg (pow_nonneg xn 5)
    (show 0≤66200-76796*x by linarith only [high])
  have r7 := mul_nonneg (pow_nonneg xn 7)
    (show 0≤29000-26889*x by linarith only [high])
  have decomposition : secondPolynomial x = f x+4*x^2+
      x^3*(30600-73214*x)+x^5*(66200-76796*x)+x^7*(29000-26889*x) := by
    dsimp only [secondPolynomial,f]; ring
  linarith only [decomposition,base,r3,r5,r7,sq_nonneg x]

theorem half_upper {c s : ℝ} (h : Normal c s) :
    0≤C1092WallProfileScalars.half c s ∧ C1092WallProfileScalars.half c s≤5/12 := by
  have b := normal_bounds h
  have data := C1092WallProfileScalars.quarter_data c s
    (by linarith only [b.1]) h.1 h.2.2
  let x := C1092WallProfileScalars.half c s
  have xn : 0≤x := data.1
  have scale : 0≤1+x^2 := by nlinarith only [sq_nonneg x]
  have product := mul_nonneg scale (sub_nonneg.mpr h.2.1)
  have diagonal : 0≤1-2*x-x^2 := by
    have cform := data.2.2.2.1
    have sform := data.2.2.2.2
    change (1+x^2)*c=1-x^2 at cform
    change (1+x^2)*s=2*x at sform
    nlinarith only [product,cform,sform]
  refine ⟨data.1,?_⟩
  change x≤5/12
  apply le_of_not_gt
  intro bad
  have excess := mul_pos (show 0<x-5/12 by linarith only [bad])
    (show 0<x+5/12+2 by linarith only [xn])
  nlinarith only [excess,diagonal]

theorem half_lower_of_tilt {c s : ℝ} (h : Normal c s) (tilt : 9*c≤35*s) :
    1/8≤C1092WallProfileScalars.half c s := by
  have b := normal_bounds h
  have data := C1092WallProfileScalars.quarter_data c s
    (by linarith only [b.1]) h.1 h.2.2
  let x := C1092WallProfileScalars.half c s
  have xn : 0≤x := data.1
  have product := mul_nonneg (show 0≤1+x^2 by nlinarith only [sq_nonneg x])
    (show 0≤35*s-9*c by linarith only [tilt])
  have necessary : 9≤70*x+9*x^2 := by
    have cform := data.2.2.2.1
    have sform := data.2.2.2.2
    change (1+x^2)*c=1-x^2 at cform
    change (1+x^2)*s=2*x at sform
    nlinarith only [product,cform,sform]
  change 1/8≤x
  apply le_of_not_gt
  intro bad
  have power := pow_le_pow_left₀ xn (le_of_lt bad) 2
  norm_num at power
  nlinarith only [necessary,bad,power]

/-- A coefficient vector in the closed unit disk gives a nonnegative
unit-normal margin. The square identity retains every endpoint. -/
theorem disk_margin (A B C t : ℝ) (unit : C^2+t^2=1)
    (disk : A^2+B^2≤1) : 0≤1+C*A+t*B := by
  have identity : (C*A+t*B)^2+(t*A-C*B)^2=(A^2+B^2)*(C^2+t^2) := by ring
  rw [unit,mul_one] at identity
  have bound : (C*A+t*B)^2≤1 := by
    nlinarith only [identity,disk,sq_nonneg (t*A-C*B)]
  nlinarith only [bound,sq_nonneg (1+C*A+t*B)]

theorem circle_arc {c s : ℝ} (h : Normal c s) : 1+(4/5)*c*s≤c+s := by
  have b := normal_bounds h
  have product := mul_nonneg (sub_nonneg.mpr b.2.2.2.2.1)
    (sub_nonneg.mpr b.2.2.2.2.2)
  have cs := mul_nonneg (show 0≤c by linarith only [b.1]) h.1
  nlinarith only [product,h.2.2,cs]

end
end N12Compact.C868.UpperGapScalars
