import Compact.Completion.C981.SupportForms

/-! C581 §§6 and 8. Both separators refer to one physical right square.
The determinant combination cancels its two position coordinates, and the
right-owned support floors yield explicit division-free wall excesses.
All separators are weak, so closed boundary contacts remain included. -/
namespace N12Compact.Completion.OtherCases.C983.NegativeWallElimination
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

def correction (R : OpenSquare) (x y : ℝ) : ℝ :=
  min (x*R.c+y*R.s) 0+min (-x*R.s+y*R.c) 0

def delta (R : OpenSquare) (x y z w : ℝ) : ℝ :=
  (x*w+y*z)*(R.c-R.s)-w*correction R x y-y*correction R z (-w)

private theorem twice_min (a : ℝ) : 2*min a 0=a-|a| := by
  rcases le_total a 0 with h | h
  · rw [min_eq_left h,abs_of_nonpos h]
    ring
  · rw [min_eq_right h,abs_of_nonneg h]
    ring

theorem lower_formula (R : OpenSquare) (x y : ℝ) :
    lower R x y=(x*R.c+y*R.s)*R.loU+(-x*R.s+y*R.c)*R.loV+
      R.side*correction R x y := by
  rw [C981CompletionSupportForms.lower_in_bands]
  dsimp only [correction]
  have first := twice_min (x*R.c+y*R.s)
  have second := twice_min (-x*R.s+y*R.c)
  linear_combination -(R.side/2)*first-(R.side/2)*second

/-- Equations (24)--(25), including zero weight `w=0`. No quotient,
independently moved square, or additional physical wall is used. -/
theorem eliminate (E N R : OpenSquare) (x y z w : ℝ)
    (side : 1<R.side) (ap : 0<R.c) (sn : R.s≤0)
    (wall : R.c*(R.loU+R.side)-R.s*(R.loV+R.side)≤2)
    (xn : 0≤x) (yp : 0<y) (zp : 0<z) (wn : 0≤w)
    (south : upper E x y≤lower R x y)
    (north : upper N z (-w)≤lower R z (-w)) :
    w*upper E x y+y*upper N z (-w)+R.side*delta R x y z w≤2*(x*w+y*z) ∧
      0<delta R x y z w ∧
      w*upper E x y+y*upper N z (-w)+delta R x y z w-2*(x*w+y*z)<0 := by
  have determinant : 0<x*w+y*z :=
    add_pos_of_nonneg_of_pos (mul_nonneg xn wn) (mul_pos yp zp)
  have ms : correction R x y≤0 := add_nonpos (min_le_right _ _) (min_le_right _ _)
  have mn : correction R z (-w)≤0 := add_nonpos (min_le_right _ _) (min_le_right _ _)
  have ws := mul_nonpos_of_nonneg_of_nonpos wn ms
  have yn := mul_nonpos_of_nonneg_of_nonpos yp.le mn
  have positive : 0<delta R x y z w := by
    have base := mul_pos determinant (show 0<R.c-R.s by linarith only [ap,sn])
    dsimp only [delta]
    linarith only [base,ws,yn]
  have identity : w*lower R x y+y*lower R z (-w)+R.side*delta R x y z w=
      (x*w+y*z)*(R.c*(R.loU+R.side)-R.s*(R.loV+R.side)) := by
    rw [lower_formula,lower_formula]
    dsimp only [delta,correction]
    ring
  have bound : w*upper E x y+y*upper N z (-w)+R.side*delta R x y z w≤
      2*(x*w+y*z) := by
    calc
      _ ≤ w*lower R x y+y*lower R z (-w)+R.side*delta R x y z w :=
        add_le_add_right (add_le_add (mul_le_mul_of_nonneg_left south wn)
          (mul_le_mul_of_nonneg_left north yp.le)) _
      _ = _ := identity
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left wall determinant.le]
  have strict := mul_pos (sub_pos.mpr side) positive
  exact ⟨bound,positive,by nlinarith only [bound,strict]⟩

/-- Equation (48): the unit-normal relation is the only algebraic premise. -/
theorem universal_identity (a b u v ell : ℝ) (unit : a^2+b^2=1) :
    a*(a*(u+ell)+b*(v+ell)-2)=
      a^2*(u+b-1)+b*(a*v-a-b+1)+a*(a+b)*(ell-1)+(1-b)*(1-a)^2 := by
  linear_combination unit

/-- The two universal floors contradict the actual right wall. In
particular this proof never divides by `b` or splits off the endpoint 0. -/
theorem universal_impossible (a b u v ell : ℝ) (ap : 0<a) (bn : 0≤b)
    (unit : a^2+b^2=1) (side : 1<ell)
    (north : 1-b<u) (south : a+b-1<a*v)
    (wall : a*(u+ell)+b*(v+ell)≤2) : False := by
  have bu : b≤1 := by nlinarith only [unit,sq_nonneg a,bn]
  have first := mul_pos (sq_pos_of_pos ap) (show 0<u+b-1 by linarith only [north])
  have second := mul_nonneg bn (show 0≤a*v-a-b+1 by linarith only [south])
  have third := mul_pos (mul_pos ap (show 0<a+b by linarith only [ap,bn]))
    (sub_pos.mpr side)
  have fourth := mul_nonneg (sub_nonneg.mpr bu) (sq_nonneg (1-a))
  have scaled := mul_nonpos_of_nonneg_of_nonpos ap.le (sub_nonpos.mpr wall)
  have identity := universal_identity a b u v ell unit
  nlinarith only [identity,first,second,third,fourth,scaled]

/-- The explicit shallow first-bottom margin (52), with its closed
threshold endpoint retained. -/
theorem shallow_margin (a b : ℝ) (ap : 0<a) (bn : 0≤b)
    (unit : a^2+b^2=1) (small : b≤9/41) :
    2+34/8405≤(26/25)*a^2+(4/5)*b^2-2*a*b+a+2*b := by
  have ah : a≤1 := by nlinarith only [unit,sq_nonneg b,ap]
  have bs : b^2≤81/1681 := by
    have product := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤9/41+b by linarith only [bn])
    nlinarith only [product]
  have al : 40/41≤a := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (sub_pos.mpr bad)
      (show 0<40/41+a by linarith only [ap])
    nlinarith only [unit,bs,product]
  have product : (1-a)*(1-2*b)≤1/41 := by
    calc
      _ ≤ (1-a)*1 := mul_le_mul_of_nonneg_left
        (by linarith only [bn]) (sub_nonneg.mpr ah)
      _ ≤ _ := by linarith only [al]
  have identity : (26/25)*a^2+(4/5)*b^2-2*a*b+a+2*b-2=
      1/25-(1-a)*(1-2*b)-(6/25)*b^2 := by
    linear_combination (26/25)*unit
  nlinarith only [identity,product,bs]

theorem shallow_impossible (a b u v ell : ℝ) (ap : 0<a) (bn : 0≤b)
    (unit : a^2+b^2=1) (side : 1<ell) (small : b≤9/41)
    (north : (26/25)*a-b<u) (south : 1+(4/5)*b-a<v)
    (wall : a*(u+ell)+b*(v+ell)≤2) : False := by
  have first := mul_pos ap (sub_pos.mpr north)
  have second := mul_nonneg bn (sub_nonneg.mpr south.le)
  have third := mul_pos (show 0<a+b by linarith only [ap,bn]) (sub_pos.mpr side)
  have margin := shallow_margin a b ap bn unit small
  nlinarith only [first,second,third,margin,wall]

#print axioms eliminate
#print axioms universal_impossible
#print axioms shallow_margin
end N12Compact.Completion.OtherCases.C983.NegativeWallElimination
