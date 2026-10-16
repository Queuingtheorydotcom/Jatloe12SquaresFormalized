import Compact.Completion.C1092.MMMP.FinalScalars39
import Compact.Geometry.C977CornerSectorBounds

/-! The continuous scalar inequality in NORTHEAST-UPPER-THIRD §4.3.
The monotonicity step is an exact chord identity on the unit circle.  The
remaining endpoint is the manuscript's quartic with five positive Bernstein
coefficients.  Both closed endpoints and both relative angle orders remain. -/
namespace N12Compact.C1092MMMPUpperThirdScalars
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false
noncomputable section

def margin (d r b t : ℝ) : ℝ :=
  1-b-t+(b*d+t*r)*(1-d+(2/5)*r)+(23/25)*(t*d-b*r)

def derivative (d r b t : ℝ) : ℝ :=
  t-b-(t*d-b*r)*(1-d+(2/5)*r)+(23/25)*(b*d+t*r)

theorem shallow_bounds {d r : ℝ} (dn : Normal d r) (angle : 8*r<7*d) :
    3/4<d ∧ r<2/3 := by
  have db := normal_bounds dn
  have square := mul_pos (show 0<7*d-8*r by linarith only [angle])
    (show 0<7*d+8*r by linarith only [db.1,dn.1])
  constructor
  · apply lt_of_not_ge
    intro no
    have bound := mul_nonneg (show 0≤3/4-d by linarith only [no])
      (show 0≤3/4+d by linarith only [db.1])
    nlinarith only [square,bound,dn.2.2]
  · apply lt_of_not_ge
    intro no
    have bound := mul_nonneg (show 0≤r-2/3 by linarith only [no])
      (show 0≤r+2/3 by linarith only [dn.1])
    nlinarith only [square,bound,dn.2.2]

theorem cosine_cap {b t : ℝ} (bn : Normal b t) (steep : 3/5≤t) : b≤4/5 := by
  have square := mul_nonneg (sub_nonneg.mpr steep)
    (show 0≤t+3/5 by linarith only [bn.1])
  nlinarith only [bn.2.2,square,sq_nonneg (b-4/5)]

/-- Uniform bounds for the two coefficients of a relative canonical frame.
The sine coefficient may have either sign. -/
theorem relative_bounds {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t) :
    7/10<b*d+t*r ∧ t*d-b*r<71/100 ∧ b*d+t*r≤1 ∧
      (b*d+t*r)^2+(t*d-b*r)^2=1 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  let alpha := b*d+t*r
  let beta := t*d-b*r
  have ap : 0<alpha := by
    have first := mul_pos (show 0<b by linarith only [bb.1])
      (show 0<d by linarith only [db.1])
    have last := mul_nonneg bn.1 dn.1
    dsimp [alpha]
    linarith only [first,last]
  have unit : alpha^2+beta^2=1 := by
    calc
      _ = (b^2+t^2)*(d^2+r^2) := by dsimp [alpha,beta]; ring
      _ = 1 := by rw [bn.2.2,dn.2.2]; norm_num
  have difference : 0≤alpha-beta := by
    have first := mul_nonneg (sub_nonneg.mpr bn.2.1)
      (show 0≤d by linarith only [db.1])
    have last := mul_nonneg (show 0≤b+t by linarith only [bb.1,bn.1]) dn.1
    dsimp [alpha,beta]
    nlinarith only [first,last]
  have sum : 0≤alpha+beta := by
    have first := mul_nonneg (show 0≤b by linarith only [bb.1])
      (sub_nonneg.mpr dn.2.1)
    have last := mul_nonneg bn.1 (show 0≤d+r by linarith only [db.1,dn.1])
    dsimp [alpha,beta]
    nlinarith only [first,last]
  have compare := mul_nonneg difference sum
  have lower : 7/10<alpha := by
    apply lt_of_not_ge
    intro no
    have bound := mul_nonneg (show 0≤7/10-alpha by linarith only [no])
      (show 0≤7/10+alpha by linarith only [ap])
    nlinarith only [bound,compare,unit]
  have upper : beta<71/100 := by
    apply lt_of_not_ge
    intro no
    have bound := mul_nonneg (show 0≤beta-71/100 by linarith only [no])
      (show 0≤beta+71/100 by linarith only [no])
    nlinarith only [bound,compare,unit]
  have one : alpha≤1 := by nlinarith only [unit,sq_nonneg beta,sq_nonneg (alpha-1)]
  exact ⟨lower,upper,one,unit⟩

private theorem derivative_positive {d r b t : ℝ}
    (dn : Normal d r) (bn : Normal b t) (dc : 3/4<d) (rs : r<2/3)
    (steep : 3/5≤t) : 187/2500<derivative d r b t := by
  have db := normal_bounds dn
  have relative := relative_bounds dn bn
  have bc := cosine_cap bn steep
  have base : 0≤1-d+(2/5)*r := by linarith only [db.2.1,dn.1]
  have cap : 1-d+(2/5)*r<13/25 := by linarith only [dc,rs]
  have first := mul_le_mul_of_nonneg_right relative.2.1.le base
  have last := mul_lt_mul_of_pos_left cap (by norm_num : (0:ℝ)<71/100)
  dsimp [derivative]
  nlinarith only [first,last,relative.1,bc,steep]

/-- An exact version of monotonicity in the northeast angle. -/
private theorem monotone {d r b t B T : ℝ}
    (dn : Normal d r) (bn : Normal b t) (Bn : Normal B T)
    (dc : 3/4<d) (rs : r<2/3) (steep : 3/5≤T) (order : T≤t) :
    margin d r B T≤margin d r b t := by
  let K := 1-d*(1-d+(2/5)*r)+(23/25)*r
  let L := 1-r*(1-d+(2/5)*r)-(23/25)*d
  have first := derivative_positive dn bn dc rs (le_trans steep order)
  have last := derivative_positive dn Bn dc rs steep
  have derivative1 : derivative d r b t=K*t-L*b := by dsimp [derivative,K,L]; ring
  have derivative0 : derivative d r B T=K*T-L*B := by dsimp [derivative,K,L]; ring
  have positive : 0≤K*(t+T)-L*(b+B) := by
    rw [derivative1] at first
    rw [derivative0] at last
    nlinarith only [first,last]
  have product := mul_nonneg (sub_nonneg.mpr order) positive
  have form1 : margin d r b t=1-K*b-L*t := by dsimp [margin,K,L]; ring
  have form0 : margin d r B T=1-K*B-L*T := by dsimp [margin,K,L]; ring
  have identity : (b+B)*(margin d r b t-margin d r B T)=
      (t-T)*(K*(t+T)-L*(b+B)) := by
    rw [form1,form0]
    linear_combination -K*bn.2.2+K*Bn.2.2
  have positiveSum : 0<b+B := by
    linarith only [(normal_bounds bn).1,(normal_bounds Bn).1]
  have nonnegative : 0≤margin d r b t-margin d r B T :=
    nonneg_of_mul_nonneg_right (by rw [identity]; exact product) positiveSum
  linarith only [nonnegative]

private theorem quartic_positive (w : ℝ) (wn : 0≤w) (wu : w≤1/3) :
    0<(19-104*w+220*w^2+36*w^3-319*w^4)/125 := by
  let x := 3*w
  have xn : 0≤x := by dsimp [x]; linarith only [wn]
  have xu : x≤1 := by dsimp [x]; linarith only [wu]
  have rest : 0≤1-x := sub_nonneg.mpr xu
  have h0 := pow_nonneg rest 4
  have h1 := mul_nonneg xn (pow_nonneg rest 3)
  have h2 := mul_nonneg (sq_nonneg x) (sq_nonneg (1-x))
  have h3 := mul_nonneg (pow_nonneg xn 3) rest
  have h4 := pow_nonneg xn 4
  have partition : (1-x)^4+4*x*(1-x)^3+6*x^2*(1-x)^2+4*x^3*(1-x)+x^4=1 := by ring
  have bernstein : (19-104*w+220*w^2+36*w^3-319*w^4)/125=
      (19/125)*(1-x)^4+4*(31/375)*x*(1-x)^3+
      6*(31/675)*x^2*(1-x)^2+4*(2/45)*x^3*(1-x)+(4/81)*x^4 := by
    dsimp [x]
    ring
  nlinarith only [h0,h1,h2,h3,h4,partition,bernstein]

private theorem endpoint_positive {d r : ℝ} (dn : Normal d r) (small : r≤3/5) :
    0<margin d r (4/5) (3/5) := by
  have db := normal_bounds dn
  have dc : 4/5≤d := cosine_order (by norm_num [Normal]) dn small
  let w := C1092WallProfileScalars.half d r
  have data := C1092WallProfileScalars.quarter_data d r
    (by linarith only [db.1]) dn.1 dn.2.2
  have wn : 0≤w := data.1
  have wu : w≤1/3 := by
    apply (div_le_iff₀ (show 0<1+d by linarith only [db.1])).mpr
    linarith only [small,dc]
  have den : 0<1+w^2 := by nlinarith only [sq_nonneg w]
  have dform : d=(1-w^2)/(1+w^2) := by
    apply (eq_div_iff den.ne').mpr
    nlinarith only [data.2.2.2.1]
  have rform : r=2*w/(1+w^2) := by
    apply (eq_div_iff den.ne').mpr
    nlinarith only [data.2.2.2.2]
  have identity : (1+w^2)^2*margin d r (4/5) (3/5)=
      (19-104*w+220*w^2+36*w^3-319*w^4)/125 := by
    rw [dform,rform]
    dsimp [margin]
    field_simp [den.ne']
    <;> ring
  exact pos_of_mul_pos_right (by rw [identity]; exact quartic_positive w wn wu)
    (sq_nonneg (1+w^2))

theorem neighbor_positive {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (dc : 3/4<d) (rs : r<2/3) (steep : 3/5≤t) (order : 0≤t*d-b*r) :
    0<margin d r b t := by
  by_cases small : r≤3/5
  · have endpoint := endpoint_positive dn small
    have comparison := monotone dn bn (show Normal (4/5) (3/5) by norm_num [Normal])
      dc rs (by norm_num) steep
    exact lt_of_lt_of_le endpoint comparison
  · have rp : 3/5≤r := (lt_of_not_ge small).le
    have rt : r≤t := sine_order bn dn (by nlinarith only [order])
    have comparison := monotone dn bn dn dc rs rp rt
    have dcTop := cosine_cap dn rp
    have endpoint : 0<margin d r d r := by
      have identity : margin d r d r=2-2*d-(3/5)*r := by
        dsimp [margin]
        linear_combination (1-d+(2/5)*r)*dn.2.2
      rw [identity]
      linarith only [dcTop,rs]
    exact lt_of_lt_of_le endpoint comparison

#print axioms neighbor_positive
end
end N12Compact.C1092MMMPUpperThirdScalars
