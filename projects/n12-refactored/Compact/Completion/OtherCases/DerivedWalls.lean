import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! A genuine forbidden line plus a strict point on one side supplies an
actual half-plane bound, which then applies to every closed square point. -/
namespace N12Compact.Completion.OtherCases.DerivedWalls
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

theorem vertical_right (q : OpenSquare) (x0 y0 h : ℝ)
    (anchor : q.Inside x0 y0) (right : h<x0)
    (avoid : ∀ y : ℝ,¬q.Inside h y) :
    ∀ x y,q.Inside x y → h≤x := by
  intro x y own
  apply le_of_not_gt
  intro left
  let t := (h-x)/(x0-x)
  have denominator : 0<x0-x := by linarith only [right,left]
  have positive : 0<t := div_pos (sub_pos.mpr left) denominator
  have small : t<1 := (div_lt_one denominator).mpr (by linarith only [right])
  have relation : t*(x0-x)=h-x := div_mul_cancel₀ _ denominator.ne'
  have xIdentity : (1-t)*x+t*x0=h := by nlinarith only [relation]
  have point := inside_segment q x y x0 y0 t own anchor positive.le small.le
  rw [xIdentity] at point
  exact avoid _ point

theorem closed_affine_bound (q : OpenSquare) (nx ny bound x0 y0 : ℝ)
    (wall : ∀ x y,q.Inside x y → bound≤nx*x+ny*y)
    (anchor : q.Inside x0 y0) (X Y : ℝ) (closed : ClosedInside q X Y) :
    bound≤nx*X+ny*Y := by
  have gap : 0≤nx*X+ny*Y-bound := by
    apply affine_endpoint_nonnegative 1 (nx*x0+ny*y0-(nx*X+ny*Y)) _ (by norm_num)
    intro t positive small
    have point := WallProfile.strict_closed_segment q X Y x0 y0 t closed anchor positive small
    have inequality := wall _ _ point
    nlinarith only [inequality]
  linarith only [gap]

#print axioms vertical_right
#print axioms closed_affine_bound
end N12Compact.Completion.OtherCases.DerivedWalls

