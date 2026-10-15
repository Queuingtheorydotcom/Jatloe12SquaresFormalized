import Compact.Geometry.C977CornerSectorBounds
import Mathlib.Tactic.Positivity

/-! Two continuous order comparisons for the actual bottom-to-wall
coupling. A half-angle change of variables exposes short sums of
nonnegative products on the entire ordered canonical arc. These are
algebraic identities, with no sampled angles or interval enumeration. -/
namespace N12Compact.CornerOuterOrderMonotone
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

def denominator (q t : ℝ) : ℝ := (1+q)*(1+t)
def cross (p q d t : ℝ) : ℝ := d*q-p*t
def F (p q d t : ℝ) : ℝ :=
  denominator q t*(d-p)+p*d*(q-t)
def G (p q d t : ℝ) : ℝ :=
  denominator q t*(2*cross p q d t-(q-t))-
    q*t*((d-p)+cross p q d t)

private theorem half_angle {p q : ℝ} (normal : Normal p q) :
    let x := q/(1+p)
    0≤x ∧ x≤1/2 ∧ p*(1+x^2)=1-x^2 ∧ q*(1+x^2)=2*x := by
  have b := normal_bounds normal
  have hp : 0<1+p := by linarith only [b.1]
  dsimp only
  refine ⟨div_nonneg normal.1 hp.le, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hp).mpr
    linarith only [normal.2.1,b.2.2.2.1]
  · field_simp [ne_of_gt hp]
    linear_combination (p+1)*normal.2.2
  · field_simp [ne_of_gt hp]
    linear_combination q*(p+1)*normal.2.2

private def P (x y : ℝ) : ℝ :=
  (x+y)*(1-x)*(1-y)+4*x^2*y^2
private def Q (x y : ℝ) : ℝ :=
  (x-y)+x^2*(1-x-x^2)+x^3*y*(2-3*x+3*y)+
    y^2*(3*x^2+x+1)+2*x*y

private theorem polynomial_nonnegative {x y : ℝ}
    (ylo : 0≤y) (order : y≤x) (xhi : x≤1/2) :
    0≤P x y ∧ 0≤Q x y := by
  have xlo : 0≤x := le_trans ylo order
  have xgap : 0≤1-x := by linarith only [xhi]
  have ygap : 0≤1-y := by linarith only [order,xhi]
  have gap := sub_nonneg.mpr order
  have square := mul_nonneg xlo (show 0≤1/2-x by linarith only [xhi])
  have first : 0≤1-x-x^2 := by nlinarith only [square,xhi]
  have second : 0≤2-3*x+3*y := by linarith only [xhi,ylo]
  constructor
  · unfold P
    positivity
  · unfold Q
    positivity

/-- Both coefficient differences are nonnegative for every ordered pair
of canonical normals, including zero tilt and equal angles. -/
theorem differences {p q d t : ℝ}
    (bottom : Normal p q) (wall : Normal d t) (order : t≤q) :
    0≤G p q d t-F p q d t ∧
    0≤p*F p q d t+q*G p q d t-denominator q t*cross p q d t := by
  let x := q/(1+p)
  let y := t/(1+d)
  obtain ⟨xlo,xhi,px,qx⟩ := half_angle bottom
  obtain ⟨ylo,yhi,dy,ty⟩ := half_angle wall
  change 0≤x at xlo
  change x≤1/2 at xhi
  change p*(1+x^2)=1-x^2 at px
  change q*(1+x^2)=2*x at qx
  change 0≤y at ylo
  change d*(1+y^2)=1-y^2 at dy
  change t*(1+y^2)=2*y at ty
  have pb := normal_bounds bottom
  have db := normal_bounds wall
  have pd := cosine_order bottom wall order
  have hpd : 0<1+p := by linarith only [pb.1]
  have hdd : 0<1+d := by linarith only [db.1]
  have order_scaled := mul_nonneg (sub_nonneg.mpr order) hpd.le
  have cosine_scaled := mul_nonneg bottom.1 (sub_nonneg.mpr pd)
  have xy : y≤x := by
    dsimp [x,y]
    apply (div_le_div_iff₀ hdd hpd).mpr
    nlinarith only [order_scaled,cosine_scaled]
  have dx : 0<1+x^2 := by positivity
  have dypos : 0<1+y^2 := by positivity
  have pe : p=(1-x^2)/(1+x^2) := (eq_div_iff (ne_of_gt dx)).mpr px
  have qe : q=2*x/(1+x^2) := (eq_div_iff (ne_of_gt dx)).mpr qx
  have de : d=(1-y^2)/(1+y^2) := (eq_div_iff (ne_of_gt dypos)).mpr dy
  have te : t=2*y/(1+y^2) := (eq_div_iff (ne_of_gt dypos)).mpr ty
  obtain ⟨pnonneg,qnonneg⟩ := polynomial_nonnegative ylo xy xhi
  have common : 0≤2*(1+x)*(x-y)*(1+y) := by
    have gap := sub_nonneg.mpr xy
    positivity
  constructor
  · have identity :
        (G p q d t-F p q d t)*((1+x^2)^2*(1+y^2)^2)=
          2*(1+x)*(x-y)*(1+y)*P x y := by
      unfold F G denominator cross P
      rw [pe,qe,de,te]
      field_simp [ne_of_gt dx,ne_of_gt dypos] <;> ring
    have product : 0≤(G p q d t-F p q d t)*
        ((1+x^2)^2*(1+y^2)^2) := by
      rw [identity]
      exact mul_nonneg common pnonneg
    exact (mul_nonneg_iff_of_pos_right (by positivity :
      0<(1+x^2)^2*(1+y^2)^2)).mp product
  · have identity :
        (p*F p q d t+q*G p q d t-denominator q t*cross p q d t)*
          ((1+x^2)^3*(1+y^2)^2)=
          2*(1+x)*(x-y)*(1+y)*Q x y := by
      unfold F G denominator cross Q
      rw [pe,qe,de,te]
      field_simp [ne_of_gt dx,ne_of_gt dypos] <;> ring
    have product : 0≤
        (p*F p q d t+q*G p q d t-denominator q t*cross p q d t)*
          ((1+x^2)^3*(1+y^2)^2) := by
      rw [identity]
      exact mul_nonneg common qnonneg
    exact (mul_nonneg_iff_of_pos_right (by positivity :
      0<(1+x^2)^3*(1+y^2)^2)).mp product

#print axioms differences
end N12Compact.CornerOuterOrderMonotone
