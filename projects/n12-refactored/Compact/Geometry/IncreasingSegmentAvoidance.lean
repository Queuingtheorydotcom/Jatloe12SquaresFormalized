import S12.Convex
import Mathlib.Tactic.LinearCombination

/-! An exact separating inequality from a genuinely owned foreign segment.
Both transformed coordinates increase along the segment. If it avoids the
square's open interior, either the entire segment is above the upper V face,
or its crossing of the lower U face is no lower than that upper V face.
Touching endpoints and touching faces are retained by weak inequalities. -/
namespace N12Compact.IncreasingSegmentAvoidance

open S12 S12Pilot
set_option Elab.async false

theorem dichotomy (A W : OpenSquare) (x₀ y₀ x₁ y₁ : ℝ)
    (first : W.Inside x₀ y₀) (last : W.Inside x₁ y₁)
    (du : 0 < A.c*(x₁-x₀)+A.s*(y₁-y₀))
    (dv : 0 < -A.s*(x₁-x₀)+A.c*(y₁-y₀))
    (startU : A.loU < A.c*x₁+A.s*y₁)
    (endU : A.c*x₁+A.s*y₁ < A.loU+A.side)
    (startV : A.loV < -A.s*x₀+A.c*y₀)
    (apart : ∀ x y, ¬(A.Inside x y ∧ W.Inside x y)) :
    A.loV+A.side ≤ -A.s*x₀+A.c*y₀ ∨
      (A.c*(x₁-x₀)+A.s*(y₁-y₀))*(A.loV+A.side) ≤
        (-A.s*(x₁-x₀)+A.c*(y₁-y₀))*A.loU -
          ((-A.s*(x₁-x₀)+A.c*(y₁-y₀))*(A.c*x₀+A.s*y₀) -
            (A.c*(x₁-x₀)+A.s*(y₁-y₀))*(-A.s*x₀+A.c*y₀)) := by
  let U := A.c*x₀+A.s*y₀
  let V := -A.s*x₀+A.c*y₀
  let d := A.c*(x₁-x₀)+A.s*(y₁-y₀)
  let e := -A.s*(x₁-x₀)+A.c*(y₁-y₀)
  change 0 < d at du
  change 0 < e at dv
  change A.loV < V at startV
  change A.loV+A.side ≤ V ∨ d*(A.loV+A.side) ≤ e*A.loU-(e*U-d*V)
  by_cases above : A.loV+A.side ≤ V
  · exact Or.inl above
  right
  by_contra crossing
  have crossing' : e*A.loU-(e*U-d*V) < d*(A.loV+A.side) :=
    lt_of_not_ge crossing
  have positiveV : V < A.loV+A.side := lt_of_not_ge above
  have ordered : (A.loU-U)/d < (A.loV+A.side-V)/e := by
    rw [div_lt_div_iff₀ du dv]
    linarith only [crossing']
  have starts : (A.loU-U)/d < 1 := by
    apply (div_lt_one du).mpr
    dsimp [U,d]
    linarith only [startU]
  have finishes : 0 < (A.loV+A.side-V)/e :=
    div_pos (sub_pos.mpr positiveV) dv
  let low := max 0 ((A.loU-U)/d)
  let high := min 1 ((A.loV+A.side-V)/e)
  have gap : low < high := by
    apply lt_min
    · exact max_lt (by norm_num) starts
    · exact max_lt finishes ordered
  let t := (low+high)/2
  have low_t : low < t := by dsimp [t]; linarith only [gap]
  have t_high : t < high := by dsimp [t]; linarith only [gap]
  have positive : 0 < t := lt_of_le_of_lt (le_max_left _ _) low_t
  have small : t < 1 := lt_of_lt_of_le t_high (min_le_left _ _)
  have uCross : A.loU-U < t*d := by
    apply (div_lt_iff₀ du).mp
    exact lt_of_le_of_lt (le_max_right _ _) low_t
  have vCross : t*e < A.loV+A.side-V := by
    apply (lt_div_iff₀ dv).mp
    exact lt_of_lt_of_le t_high (min_le_right _ _)
  have uRemainder := mul_pos (sub_pos.mpr small) du
  have vIncrement := mul_pos positive dv
  let x := (1-t)*x₀+t*x₁
  let y := (1-t)*y₀+t*y₁
  have owned : W.Inside x y :=
    inside_segment W x₀ y₀ x₁ y₁ t first last positive.le small.le
  have uIdentity : A.c*x+A.s*y=U+t*d := by dsimp [x,y,U,d]; ring
  have vIdentity : -A.s*x+A.c*y=V+t*e := by dsimp [x,y,V,e]; ring
  have uEnd : U+d=A.c*x₁+A.s*y₁ := by dsimp [U,d]; ring
  have inside : A.Inside x y := by
    change A.loU < A.c*x+A.s*y ∧ A.c*x+A.s*y < A.loU+A.side ∧
      A.loV < -A.s*x+A.c*y ∧ -A.s*x+A.c*y < A.loV+A.side
    rw [uIdentity,vIdentity]
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [uCross]
    · nlinarith only [uRemainder,uEnd,endU]
    · change A.loV < V+t*e
      linarith only [startV,vIncrement]
    · linarith only [vCross]
  exact apart x y ⟨inside,owned⟩

/-- The original upper-left wall segment constrains a positive central
square which misses the center through its upper U face. This is only the
stated dichotomy, not a four-square contradiction. -/
theorem left_wall (A W : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (cap : A.loU+A.side ≤ 2*(A.c+A.s))
    (below : A.Inside 2 (3/2)) (west : A.Inside (3/2) 2)
    (wallMarker : W.Inside (457/500) 2)
    (wallPoint : W.Inside 1 (113/50))
    (apart : ∀ x y, ¬(A.Inside x y ∧ W.Inside x y)) :
    A.loV+A.side ≤ 2*A.c-(457/500)*A.s ∨
      (1641/25000 : ℝ) ≤
        ((13/50)*A.c-(43/500)*A.s)*A.loU -
          ((43/500)*A.c+(13/50)*A.s)*(A.loV+A.side) := by
  have cBound : A.c ≤ 1 := by
    nlinarith only [A.unit_normal,sq_nonneg A.s,sq_nonneg (A.c-1)]
  have du : 0 < A.c*(1-457/500)+A.s*(113/50-2) := by
    linarith only [hc,hs]
  have dv : 0 < -A.s*(1-457/500)+A.c*(113/50-2) := by
    linarith only [hc,order]
  have startU : A.loU < A.c*1+A.s*(113/50) := by
    linarith only [cap,side,cBound,hs]
  have endU : A.c*1+A.s*(113/50) < A.loU+A.side := by
    linarith only [west.2.1,hc,order]
  have startV : A.loV < -A.s*(457/500)+A.c*2 := by
    linarith only [below.2.2.1,hc,hs]
  have cut := dichotomy A W (457/500) 2 1 (113/50)
    wallMarker wallPoint du dv startU endU startV apart
  have constant :
      (-A.s*(1-457/500)+A.c*(113/50-2))*(A.c*(457/500)+A.s*2) -
        (A.c*(1-457/500)+A.s*(113/50-2))*(-A.s*(457/500)+A.c*2) =
          (1641/25000 : ℝ) := by
    linear_combination (1641/25000)*A.unit_normal
  rcases cut with above | crossing
  · left; linarith only [above]
  · right
    rw [constant] at crossing
    nlinarith only [crossing]

end N12Compact.IncreasingSegmentAvoidance
