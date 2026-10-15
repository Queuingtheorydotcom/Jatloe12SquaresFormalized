import Compact.Completion.C1092.MPPMNegativeCrosspointCoefficients
import Compact.Completion.C1092.WallProfileScalars
import Compact.Completion.CommonCases.UnitCircleChord

/-! NEGATIVE-WALL-SCALARS §7: exact quartic tools. The first interval
uses a factored endpoint identity in place of differentiation. The last
interval uses the four printed Bernstein coefficients and the exact
degree-six numerator. No angular sampling or strict endpoint removal. -/
namespace N12Compact.C1092MPPMNegativeCrosspointSupport.G01Quartic
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

def poly (a0 a1 a2 a3 a4 z : ℝ) : ℝ :=
  a0+a1*z+a2*z^2+a3*z^3+a4*z^4

def T (c s A B z : ℝ) : ℝ :=
  poly (s-B) (2*(c+s-A)) (4*c-2*s) (-2*(c+s+A)) (s+B) z

/-- When the constant coefficient is nonpositive, the concave cubic
after removing that coefficient gives this exact endpoint lower bound.
The zero left endpoint is handled separately, without dividing by it. -/
theorem endpoints (a0 a1 a2 a3 a4 l R z : ℝ)
    (Rp : 0<R) (ln : 0≤l) (lR : l<R) (lz : l≤z) (zR : z≤R)
    (constant : a0≤0) (linear : 0≤a1) (fourth : 0≤a4)
    (curvature : 0≤-a3-3*R*a4)
    (left : 0≤poly a0 a1 a2 a3 a4 l)
    (right : 0≤poly a0 a1 a2 a3 a4 R) :
    0≤poly a0 a1 a2 a3 a4 z := by
  have zn : 0≤z := le_trans ln lz
  have rest : 0≤R-z := sub_nonneg.mpr zR
  have step : 0≤z-l := sub_nonneg.mpr lz
  have gap : 0<R-l := sub_pos.mpr lR
  have curve : 0≤-a3-a4*(z+l+R) := by
    have weight := mul_nonneg fourth
      (show 0≤3*R-(z+l+R) by linarith only [zR,lR])
    nlinarith only [weight,curvature]
  by_cases zero : l=0
  · have a0zero : a0=0 := by
      rw [zero] at left
      norm_num [poly] at left
      exact le_antisymm constant left
    have curve0 : 0≤-a3-a4*(z+R) := by simpa only [zero,add_zero] using curve
    have first := mul_nonneg (mul_nonneg (mul_nonneg Rp.le zn) rest) linear
    have last := mul_nonneg (sq_nonneg z) right
    have remainder := mul_nonneg
      (mul_nonneg (mul_nonneg (sq_nonneg R) (sq_nonneg z)) rest) curve0
    have identity : R^2*poly a0 a1 a2 a3 a4 z=
        R*z*(R-z)*a1+z^2*poly a0 a1 a2 a3 a4 R+
          R^2*z^2*(R-z)*(-a3-a4*(z+R)) := by
      rw [a0zero]
      dsimp [poly]
      ring
    have weighted : 0≤R^2*poly a0 a1 a2 a3 a4 z := by
      rw [identity]
      linarith only [first,last,remainder]
    exact nonneg_of_mul_nonneg_right weighted (sq_pos_of_pos Rp)
  · have lp : 0<l := lt_of_le_of_ne ln (Ne.symm zero)
    have first := mul_nonneg (mul_nonneg (mul_nonneg zn Rp.le) rest) left
    have last := mul_nonneg (mul_nonneg (mul_nonneg zn ln) step) right
    have bracket : 0≤-a0+l*R*z*(-a3-a4*(z+l+R)) := by
      have product := mul_nonneg (mul_nonneg (mul_nonneg ln Rp.le) zn) curve
      linarith only [constant,product]
    have remainder := mul_nonneg (mul_nonneg (mul_nonneg gap.le step) rest) bracket
    have identity : l*R*(R-l)*poly a0 a1 a2 a3 a4 z=
        z*R*(R-z)*poly a0 a1 a2 a3 a4 l+
          z*l*(z-l)*poly a0 a1 a2 a3 a4 R+
          (R-l)*(z-l)*(R-z)*(-a0+l*R*z*(-a3-a4*(z+l+R))) := by
      dsimp [poly]
      ring
    have weighted : 0≤l*R*(R-l)*poly a0 a1 a2 a3 a4 z := by
      rw [identity]
      linarith only [first,last,remainder]
    exact nonneg_of_mul_nonneg_right weighted (mul_pos (mul_pos lp Rp) gap)

theorem bernstein (a0 a1 a2 a3 a4 w z : ℝ) (wp : 0<w)
    (zn : 0≤z) (zw : z≤w)
    (b0 : 0≤a0) (b1 : 0≤a0+a1*w/4)
    (b2 : 0≤a0+a1*w/2+a2*w^2/6)
    (b3 : 0≤a0+3*a1*w/4+a2*w^2/2+a3*w^3/4)
    (b4 : 0≤poly a0 a1 a2 a3 a4 w) :
    0≤poly a0 a1 a2 a3 a4 z := by
  have rest : 0≤w-z := sub_nonneg.mpr zw
  have first := mul_nonneg b0 (pow_nonneg rest 4)
  have second := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) b1) zn)
    (pow_nonneg rest 3)
  have third := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤6) b2)
    (sq_nonneg z)) (sq_nonneg (w-z))
  have fourth := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤4) b3)
    (pow_nonneg zn 3)) rest
  have last := mul_nonneg b4 (pow_nonneg zn 4)
  have identity : w^4*poly a0 a1 a2 a3 a4 z=
      a0*(w-z)^4+4*(a0+a1*w/4)*z*(w-z)^3+
        6*(a0+a1*w/2+a2*w^2/6)*z^2*(w-z)^2+
        4*(a0+3*a1*w/4+a2*w^2/2+a3*w^3/4)*z^3*(w-z)+
        poly a0 a1 a2 a3 a4 w*z^4 := by dsimp [poly]; ring
  have weighted : 0≤w^4*poly a0 a1 a2 a3 a4 z := by
    rw [identity]
    linarith only [first,second,third,fourth,last]
  exact nonneg_of_mul_nonneg_right weighted (pow_pos wp 4)

theorem steep_bounds {c s : ℝ} (cn : Normal c s) (steep : 3/5≤s) :
    c≤4/5 ∧ s≤5/7 ∧ 3*c+s≤3 := by
  have cb := normal_bounds cn
  have cp : 0≤c := by linarith only [cb.1]
  have csum := mul_nonneg (sub_nonneg.mpr cn.2.1) (add_nonneg cp cn.1)
  have scut := mul_nonneg (sub_nonneg.mpr steep)
    (show 0≤s+3/5 by linarith only [cn.1])
  have fixed : Normal (4/5:ℝ) (3/5) := by norm_num [Normal]
  have chord := CommonCases.UnitCircleChord.decreasing (A := (3:ℝ)) (B := 1)
    (show (0:ℝ)<4/5 by norm_num) cp fixed.2.2 cn.2.2 fixed.1 cn.1 steep
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨by nlinarith only [cn.2.2,scut,sq_nonneg (c-4/5)],
    by nlinarith only [cn.2.2,csum,sq_nonneg (s-5/7)],by linarith only [chord]⟩

theorem half_bound {d t : ℝ} (en : Normal d t) (shallow : 8*t≤3*d) :
    half d t≤2/11 := by
  have eb := normal_bounds en
  have data := quarter_data d t (by linarith only [eb.1]) en.1 en.2.2
  let w := half d t
  have weighted := mul_le_mul_of_nonneg_left shallow (show 0≤1+w^2 by positivity)
  have quadratic : 16*w≤3-3*w^2 := by
    nlinarith only [weighted,data.2.2.2.1,data.2.2.2.2]
  apply le_of_not_gt
  intro high
  have increasing := mul_pos (show 0<w-2/11 by linarith only [high])
    (show 0<3*w+6/11+16 by linarith only [data.1])
  nlinarith only [increasing,quadratic]

private theorem numerator (w : ℝ) (wn : 0≤w) (wu : w≤2/11) :
    0<61-130*w-203*w^2-390*w^3-545*w^4-525*w^6 := by
  have b2 : w^2≤(2/11:ℝ)^2 := by
    have gap := mul_nonneg (sub_nonneg.mpr wu)
      (show 0≤2/11+w by linarith only [wn])
    nlinarith only [gap]
  have b3 : w^3≤(2/11:ℝ)^3 := by
    have bound := mul_le_mul b2 wu wn (by norm_num : (0:ℝ)≤(2/11)^2)
    nlinarith only [bound]
  have b4 : w^4≤(2/11:ℝ)^4 := by
    have bound := mul_le_mul b2 b2 (sq_nonneg w) (by norm_num : (0:ℝ)≤(2/11)^2)
    nlinarith only [bound]
  have b6 : w^6≤(2/11:ℝ)^6 := by
    have bound := mul_le_mul b3 b3 (pow_nonneg wn 3) (by norm_num : (0:ℝ)≤(2/11)^3)
    nlinarith only [bound]
  nlinarith only [wu,b2,b3,b4,b6]

/-- The exact common lower coefficient in (32), with its positive
denominators cleared. This formulation also retains the zero-angle case. -/
theorem lower_coefficient (d t : ℝ) (en : Normal d t) (shallow : 8*t≤3*d) :
    0≤t*(1-(61/100)*d-(13/20)*t)+
      (3/2)*(1/3-P2 d t)*half d t-(21/8)*(half d t)^3 := by
  have eb := normal_bounds en
  let w := half d t
  have data := quarter_data d t (by linarith only [eb.1]) en.1 en.2.2
  have wn : 0≤w := data.1
  have wu : w≤2/11 := half_bound en shallow
  have Dp : 0<1+w^2 := by positivity
  have dform : d=(1-w^2)/(1+w^2) := by
    apply (eq_div_iff Dp.ne').mpr
    nlinarith only [data.2.2.2.1]
  have tform : t=2*w/(1+w^2) := by
    apply (eq_div_iff Dp.ne').mpr
    nlinarith only [data.2.2.2.2]
  have identity : t*(1-(61/100)*d-(13/20)*t)+
      (3/2)*(1/3-P2 d t)*w-(21/8)*w^3=
      w*(61-130*w-203*w^2-390*w^3-545*w^4-525*w^6)/(200*(1+w^2)^2) := by
    rw [dform,tform]
    dsimp [P2]
    field_simp [Dp.ne'] <;> ring
  change 0≤t*(1-(61/100)*d-(13/20)*t)+(3/2)*(1/3-P2 d t)*w-(21/8)*w^3
  rw [identity]
  exact div_nonneg (mul_nonneg wn (numerator w wn wu).le) (by positivity)

theorem parameter_identity (c s A B h r : ℝ) (q : Quarter h r) :
    T c s A B (half r h)=(1+(half r h)^2)^2*
      ((c-s)*h^2+(c+s)*h*r+s-A*h-B*r) := by
  let z := half r h
  have data := quarter_data r h q.sine q.cosine (by nlinarith only [q.unit])
  have Dp : 0<1+z^2 := by positivity
  have hform : h=2*z/(1+z^2) := by
    apply (eq_div_iff Dp.ne').mpr
    nlinarith only [data.2.2.2.2]
  have rform : r=(1-z^2)/(1+z^2) := by
    apply (eq_div_iff Dp.ne').mpr
    nlinarith only [data.2.2.2.1]
  change T c s A B z=(1+z^2)^2*((c-s)*h^2+(c+s)*h*r+s-A*h-B*r)
  rw [hform,rform]
  dsimp [T,poly]
  field_simp [Dp.ne'] <;> ring

theorem parameter_bound {h r : ℝ} (q : Quarter h r) (order : h≤r) :
    half r h≤5/12 := by
  have data := quarter_data r h q.sine q.cosine (by nlinarith only [q.unit])
  let z := half r h
  have weighted := mul_le_mul_of_nonneg_left order (show 0≤1+z^2 by positivity)
  have quadratic : z^2+2*z≤1 := by
    nlinarith only [data.2.2.2.1,data.2.2.2.2,weighted]
  apply le_of_not_gt
  intro high
  have gap := mul_pos (show 0<z-5/12 by linarith only [high])
    (show 0<z+5/12+2 by linarith only [data.1])
  nlinarith only [quadratic,gap]

theorem parameter_order (d t h r : ℝ) (en : Normal d t) (q : Quarter h r) :
    (1+(half d t)^2)*(1+(half r h)^2)*deltaE d t h r=
      2*(half d t-half r h)*(1+half d t*half r h) := by
  have eb := normal_bounds en
  have ed := quarter_data d t (by linarith only [eb.1]) en.1 en.2.2
  have bd := quarter_data r h q.sine q.cosine (by nlinarith only [q.unit])
  calc
    _ = ((1+(half d t)^2)*t)*((1+(half r h)^2)*r)-
        ((1+(half d t)^2)*d)*((1+(half r h)^2)*h) := by dsimp [deltaE]; ring
    _ = _ := by rw [ed.2.2.2.1,ed.2.2.2.2,bd.2.2.2.1,bd.2.2.2.2]; ring

end
end N12Compact.C1092MPPMNegativeCrosspointSupport.G01Quartic
