import Compact.Completion.OtherCases.WallProfile.SupportGeometry
import S12.Convex
import Mathlib.Tactic.LinearCombination

/-! Exact closed vertices, actual segment interiors and wall limits used
by the continuous corner-to-wall transfer. -/
namespace N12Compact.Completion.OtherCases.WallProfile
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

theorem vertex (q : OpenSquare) (U V : ℝ)
    (hu : q.loU ≤ U ∧ U ≤ q.loU+q.side)
    (hv : q.loV ≤ V ∧ V ≤ q.loV+q.side) :
    ClosedInside q (q.c*U-q.s*V) (q.s*U+q.c*V) := by
  have u : q.c*(q.c*U-q.s*V)+q.s*(q.s*U+q.c*V)=U := by
    linear_combination U*q.unit_normal
  have v : -q.s*(q.c*U-q.s*V)+q.c*(q.s*U+q.c*V)=V := by
    linear_combination V*q.unit_normal
  dsimp [ClosedInside]
  rw [u,v]
  exact ⟨hu.1,hu.2,hv.1,hv.2⟩

theorem strict_closed_segment (q : OpenSquare) (x y x' y' t : ℝ)
    (closed : ClosedInside q x y) (strict : q.Inside x' y')
    (positive : 0 < t) (small : t < 1) :
    q.Inside ((1-t)*x+t*x') ((1-t)*y+t*y') := by
  have remaining : 0 ≤ 1-t := by linarith only [small]
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [mul_nonneg remaining (sub_nonneg.mpr closed.1),
      mul_pos positive (sub_pos.mpr strict.1)]
  · nlinarith only [mul_nonneg remaining (sub_nonneg.mpr closed.2.1),
      mul_pos positive (sub_pos.mpr strict.2.1)]
  · nlinarith only [mul_nonneg remaining (sub_nonneg.mpr closed.2.2.1),
      mul_pos positive (sub_pos.mpr strict.2.2.1)]
  · nlinarith only [mul_nonneg remaining (sub_nonneg.mpr closed.2.2.2),
      mul_pos positive (sub_pos.mpr strict.2.2.2)]

theorem vertical_owned (q : OpenSquare) (x b h : ℝ) (gap : b < h)
    (bottom : q.Inside x b) (top : q.Inside x h) :
    ∀ y : ℝ, b ≤ y → y ≤ h → q.Inside x y := by
  intro y lower upper
  let t := (y-b)/(h-b)
  have denominator : 0 < h-b := sub_pos.mpr gap
  have tn : 0 ≤ t := div_nonneg (sub_nonneg.mpr lower) denominator.le
  have tu : t ≤ 1 := (div_le_iff₀ denominator).mpr (by linarith only [upper])
  have relation : t*(h-b)=y-b := div_mul_cancel₀ _ denominator.ne'
  have point := inside_segment q x b x h t bottom top tn tu
  have first : (1-t)*x+t*x=x := by ring
  have second : (1-t)*b+t*h=y := by nlinarith only [relation]
  simpa only [first,second] using point

/-- The bottom wall bounds this actual closed vertex, even when the
canonical sine is negative. No first-coordinate wall is added. -/
theorem lower_wall_vertex (q : OpenSquare)
    (wall : ∀ x y, q.Inside x y → 0 ≤ y) :
    0 ≤ q.s*(q.loU+q.side)+q.c*q.loV := by
  apply affine_endpoint_nonnegative q.side (q.c-q.s) _ q.side_pos
  intro t positive small
  let u := q.loU+q.side-t
  let v := q.loV+t
  have inside : q.Inside (q.c*u-q.s*v) (q.s*u+q.c*v) := by
    apply (inside_iff_rotated_box q _ _).mpr
    refine ⟨u,v,?_,rfl,rfl⟩
    dsimp only [u,v,InBands]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [positive,small]
  have bound := wall _ _ inside
  dsimp only [u,v] at bound
  nlinarith only [bound]

theorem radius_even (q : OpenSquare) (nx ny : ℝ) :
    supportRadius q (-nx) (-ny)=supportRadius q nx ny := by
  have first : (-nx)*q.c+(-ny)*q.s=-(nx*q.c+ny*q.s) := by ring
  have second : -(-nx)*q.s+(-ny)*q.c=-(-nx*q.s+ny*q.c) := by ring
  simp only [supportRadius,first,second,abs_neg]

theorem upper_neg (q : OpenSquare) (nx ny : ℝ) :
    upper q (-nx) (-ny)= -lower q nx ny := by
  unfold upper lower
  rw [radius_even]
  ring

theorem lower_neg (q : OpenSquare) (nx ny : ℝ) :
    lower q (-nx) (-ny)= -upper q nx ny := by
  unfold upper lower
  rw [radius_even]
  ring

/-- Any nonaxis square has a down-right first face normal after physical
face reindexing. The two component magnitudes need not be ordered. -/
theorem negative_frame (q : OpenSquare) :
    ∃ r : OpenSquare, 0 < r.c ∧ r.s ≤ 0 ∧ r.side=q.side ∧
      (∀ x y, r.Inside x y ↔ q.Inside x y) := by
  obtain ⟨r,cp,tn,shape,inside,_⟩ := positive_frame q
  by_cases axis : r.s=0
  · exact ⟨r,cp,by rw [axis],shape,inside⟩
  · have tp : 0 < r.s := lt_of_le_of_ne tn (Ne.symm axis)
    refine ⟨turnFrame (turnFrame (turnFrame r)),?_,?_,by simpa using shape,?_⟩
    · simpa only [turnFrame,neg_neg] using tp
    · simp only [turnFrame,neg_neg]
      exact le_of_lt (neg_neg_of_pos cp)
    · intro x y; simpa only [turnFrame_inside] using inside x y

end N12Compact.Completion.OtherCases.WallProfile

