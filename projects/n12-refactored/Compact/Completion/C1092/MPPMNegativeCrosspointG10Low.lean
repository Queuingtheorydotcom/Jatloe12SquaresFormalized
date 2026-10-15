import Compact.Completion.C1092.MPPMNegativeCrosspointClamp
import Compact.Completion.C1092.WallProfileScalars

/-! NEGATIVE-WALL-SCALARS G10 below the diagonal. The small-angle
quartic has an explicit positive quadratic minorant; the middle interval
is exactly the already proved central G00 at the same boundary normal. -/
namespace N12Compact.C1092MPPMNegativeCrosspointSupport
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem G10_before (c s d t h r : ℝ) (en : Normal d t)
    (q : Quarter h r) (order : deltaE d t h r≤0) :
    G10 c s d t h r=
      t*(h*(h+r-2)-FC c s h r-(13/50)*r)+d*r*(h+r-1) := by
  dsimp [G10]
  rw [abs_of_nonpos order]
  dsimp [kE,deltaE,E0]
  linear_combination -(t/2)*q.unit

private theorem low_polynomial {h r : ℝ} (q : Quarter h r)
    (hh : 4/5≤h) (rr : r≤3/5) :
    0<r*(h+r-1)+(3/8)*(h*(h+r-21/25)-(57/50)*r) := by
  have data := quarter_data h r q.cosine q.sine q.unit
  let z := half h r
  have zp : 0≤z := data.1
  have zu : z≤1/3 := by
    apply (div_le_iff₀ (by linarith only [hh] : 0<1+h)).mpr
    linarith only [rr,hh]
  have den : 0<1+z^2 := by positivity
  have hf : h=(1-z^2)/(1+z^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.1])
  have rf : r=2*z/(1+z^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.2])
  have cubic := mul_nonneg (sq_nonneg z) (show 0≤1/3-z by linarith only [zu])
  have quartic := pow_nonneg zp 4
  have positive : 0<(829/3)*z^2-21*z+12 := by
    have identity : (829/3)*z^2-21*z+12=
        (829/3)*(z-63/1658)^2+38469/3316 := by ring
    rw [identity]
    positivity
  have polynomial : 0<138*z^4-1121*z^3+650*z^2-21*z+12 := by
    nlinarith only [cubic,quartic,positive]
  have identity : 200*(1+z^2)^2*
      (r*(h+r-1)+(3/8)*(h*(h+r-21/25)-(57/50)*r))=
        138*z^4-1121*z^3+650*z^2-21*z+12 := by
    rw [hf,rf]
    field_simp [den.ne']
    <;> ring
  have weighted : 0<200*(1+z^2)^2*
      (r*(h+r-1)+(3/8)*(h*(h+r-21/25)-(57/50)*r)) := by
    rw [identity]
    exact polynomial
  exact pos_of_mul_pos_right weighted (by positivity)

theorem G10_low_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (shallow : 8*t≤3*d)
    (q : Quarter h r) (hh : 4/5≤h) (rr : r≤3/5) :
    0≤G10 c s d t h r := by
  have eb := normal_bounds en
  have sb := shallow_bounds en shallow
  have upper : h+r≥1 := by
    have product := mul_nonneg q.cosine q.sine
    nlinarith only [q.unit,product,sq_nonneg (h+r-1),q.cosine,q.sine]
  have first := mul_nonneg (show 0≤9/25-t by linarith only [sb.2]) q.sine
  have last := mul_nonneg (show 0≤d-93/100 by linarith only [sb.1]) q.cosine
  have order : deltaE d t h r≤0 := by
    dsimp [deltaE]
    nlinarith only [first,last,rr,hh]
  have cap := FC_low_cap c s h r cn steep q hh rr
  have weighted := mul_le_mul_of_nonneg_left cap en.1
  let A := h*(h+r-21/25)-(57/50)*r
  let B := r*(h+r-1)
  have Bn : 0≤B := mul_nonneg q.sine (sub_nonneg.mpr upper)
  have bound : t*A+d*B≤G10 c s d t h r := by
    rw [G10_before c s d t h r en q order]
    dsimp [A,B]
    nlinarith only [weighted]
  by_cases sign : 0≤A
  · have first := mul_nonneg en.1 sign
    have last := mul_nonneg (show 0≤d by linarith only [eb.1]) Bn
    linarith only [first,last,bound]
  · have margin := low_polynomial q hh rr
    change 0<B+(3/8)*A at margin
    have first := mul_nonneg (show 0≤3*d/8-t by linarith only [shallow])
      (show 0≤-A by linarith only [sign])
    have last := mul_nonneg (show 0≤d by linarith only [eb.1]) margin.le
    nlinarith only [first,last,bound]

theorem G10_middle_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (shallow : 8*t≤3*d)
    (bn : Normal h r) (bs : 3/5≤r) : 0≤G10 c s d t h r := by
  have cap := FC_middle_cap c s h r cn steep bn bs
  have weighted := mul_le_mul_of_nonneg_left cap en.1
  have central := G00_nonnegative bn en bs shallow
    (show Quarter h r from ⟨by linarith only [(normal_bounds bn).1],bn.1,bn.2.2⟩)
  have self : kC h r h r=1 := by dsimp [kC]; nlinarith only [bn.2.2]
  have zero : deltaC h r h r=0 := by dsimp [deltaC]; ring
  dsimp [G00,width] at central
  rw [self,zero,abs_zero] at central
  dsimp [G10,ell,kE,C0] at *
  nlinarith only [central,weighted]

end
#print axioms G10_low_nonnegative
#print axioms G10_middle_nonnegative
end N12Compact.C1092MPPMNegativeCrosspointSupport
