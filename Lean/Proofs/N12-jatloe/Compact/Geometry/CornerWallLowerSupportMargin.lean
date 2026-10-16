import Compact.Geometry.C977CornerSectorBounds

/-! One continuous lower-support margin for a right wall missing its
actual upper corner. The two-angle minimum occurs at equal normals.
Only a linear functional on a unit-circle arc is compared. -/
namespace N12Compact.CornerWallLowerSupportMargin

open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

noncomputable def F (c s d t : ℝ) : ℝ :=
  1-2*c-s+s*(1-t)/d+(c*d+s*t)+max (c*t-s*d) 0

theorem diagonal_minimum {c s d t : ℝ}
    (bn : Normal c s) (rn : Normal d t) :
    (1-d)^2+(1-d)*t*(1-t)/d≤F c s d t := by
  have rb := normal_bounds rn
  have dp : 0<d := by linarith only [rb.1]
  let H := (1-d)*(1-t)/d
  have hid : d*H=(1-d)*(1-t) := by
    dsimp [H]
    field_simp [ne_of_gt dp] <;> ring
  have hp : 0≤H := div_nonneg
    (mul_nonneg (sub_nonneg.mpr rb.2.1) (sub_nonneg.mpr rb.2.2.2.1)) dp.le
  have expression : F c s d t=1-(2-d)*c+H*s+max (c*t-s*d) 0 := by
    dsimp [F,H]
    field_simp [ne_of_gt dp] <;> ring
  have endpoint : (1-d)^2+(1-d)*t*(1-t)/d=1-(2-d)*d+H*t := by
    dsimp [H]
    ring
  rw [endpoint]
  rcases le_total s t with order | order
  · have cosine : d≤c := cosine_order rn bn order
    have first := mul_nonneg
      (show 0≤c by linarith only [bn.1,bn.2.1]) (sub_nonneg.mpr order)
    have second := mul_nonneg bn.1 (sub_nonneg.mpr cosine)
    have cross : 0≤c*t-s*d := by nlinarith only [first,second]
    rw [max_eq_left cross] at expression
    let P := 2-d-t
    let Q := d-H
    have pp : 0≤P := by dsimp [P]; linarith only [rb.2.2.2.2.2]
    have slope : P*t≤Q*d := by
      dsimp [P,Q]
      nlinarith only [hid,rn.2.2,rn.2.1]
    have arc := linear_arc_max rn bn order pp slope
    dsimp [P,Q] at arc
    nlinarith only [arc,expression]
  · have cosine : c≤d := cosine_order bn rn order
    have first := mul_nonneg dp.le (sub_nonneg.mpr order)
    have second := mul_nonneg rn.1 (sub_nonneg.mpr cosine)
    have cross : c*t-s*d≤0 := by nlinarith only [first,second]
    rw [max_eq_right cross] at expression
    have cosineWeight := mul_nonneg
      (show 0≤2-d by linarith only [rb.2.1]) (sub_nonneg.mpr cosine)
    have sineWeight := mul_nonneg hp (sub_nonneg.mpr order)
    nlinarith only [expression,cosineWeight,sineWeight]

theorem margin {c s d t : ℝ} (bn : Normal c s) (rn : Normal d t) :
    0≤F c s d t := by
  have bounds := normal_bounds rn
  have remainder : 0≤(1-d)*t*(1-t)/d := div_nonneg
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr bounds.2.1) rn.1)
      (sub_nonneg.mpr bounds.2.2.2.1))
    (by linarith only [bounds.1])
  exact le_trans (add_nonneg (sq_nonneg (1-d)) remainder) (diagonal_minimum bn rn)

#print axioms diagonal_minimum
#print axioms margin
end N12Compact.CornerWallLowerSupportMargin
