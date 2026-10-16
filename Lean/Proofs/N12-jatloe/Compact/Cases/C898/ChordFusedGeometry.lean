import Compact.Cases.C898.ChordPlans
import Compact.Geometry.ThreeSquareSupport

/-! Both C898 central-square chord exclusions have a predetermined side.
The original two bottom markers bound the center uniformly over orientation;
the two independent windows can therefore be applied to the same original
pose, without an intermediate owner5 domain. -/

namespace N12Compact.C898Chord.Fused

open S12 S12Pilot FourSquareAnchors ThreeSquare AngleSection C898Shared
open IntegerSupport CoordinateBound

def leftLo : ℚ := 77541931/50000000
def leftHi : ℚ := 79616259/50000000
def rightLo : ℚ := 252785619/100000000
def rightHi : ℚ := 25285449/10000000

theorem central_center_bounds (q : OpenSquare) (cap : q.side ≤ 1001/1000)
    (left : ClosedInside q (33/20) (33/20))
    (right : ClosedInside q (47/20) (33/20)) :
    (6397/4000 : ℝ) ≤ centerX q ∧ centerX q ≤ 9603/4000 := by
  have sum : |q.c| + |q.s| ≤ 3/2 := by
    nlinarith [q.unit_normal, sq_abs q.c, sq_abs q.s,
      sq_nonneg (|q.c| - |q.s|)]
  have width := mul_le_mul cap sum (add_nonneg (abs_nonneg q.c) (abs_nonneg q.s))
    (by norm_num : (0 : ℝ) ≤ 1001/1000)
  have hleft := (abs_le.mp (closed_support q (33/20) (33/20) 1 0 left)).1
  have hright := (abs_le.mp (closed_support q (47/20) (33/20) 1 0 right)).2
  simp only [supportRadius, one_mul, zero_mul, add_zero, neg_mul, abs_neg]
    at hleft hright
  constructor <;> nlinarith only [width, hleft, hright]

/-- The left window forces the center to its right for every source angle. -/
theorem left_window (q : Fin 4 → OpenSquare) (source : Fin poseCount)
    (ha : ∀ i, 1 < (q i).side) (hb : ∀ i, InsideContainer (q i))
    (hd : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (cap : (q 0).side ≤ 1001/1000)
    (left : ClosedInside (q 0) (33/20) (33/20))
    (right : ClosedInside (q 0) (47/20) (33/20))
    (hs : (poses source).OrientedRealizes (q 0))
    (neighbors : ∀ x, (leftLo : ℝ) ≤ x → x ≤ (leftHi : ℝ) →
      ∀ i : Fin 3, VerticalSection (q i.succ) x) :
    ((leftHi + (poseRadius source).radius : ℚ) : ℝ) < centerX (q 0) := by
  have bounds := central_center_bounds (q 0) cap left right
  have radius : (0 : ℝ) ≤ (poseRadius source).radius := by
    exact_mod_cast (pose_radius_checked source).1
  have excluded := window_excludes (leftLo : ℝ) (leftHi : ℝ)
    (by norm_num [leftLo, leftHi]) q (poses source) (poseRadius source)
    (pose_radius_checked source) ha hb hd hs neighbors
  push_cast
  apply lt_of_not_ge
  intro upper
  apply excluded
  constructor
  · norm_num [leftLo] at ⊢
    linarith only [bounds.1, radius]
  · exact upper

/-- The right window forces the center to its left for every source angle. -/
theorem right_window (q : Fin 4 → OpenSquare) (source : Fin poseCount)
    (ha : ∀ i, 1 < (q i).side) (hb : ∀ i, InsideContainer (q i))
    (hd : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (cap : (q 0).side ≤ 1001/1000)
    (left : ClosedInside (q 0) (33/20) (33/20))
    (right : ClosedInside (q 0) (47/20) (33/20))
    (hs : (poses source).OrientedRealizes (q 0))
    (neighbors : ∀ x, (rightLo : ℝ) ≤ x → x ≤ (rightHi : ℝ) →
      ∀ i : Fin 3, VerticalSection (q i.succ) x) :
    centerX (q 0) < ((rightLo - (poseRadius source).radius : ℚ) : ℝ) := by
  have bounds := central_center_bounds (q 0) cap left right
  have radius : (0 : ℝ) ≤ (poseRadius source).radius := by
    exact_mod_cast (pose_radius_checked source).1
  have excluded := window_excludes (rightLo : ℝ) (rightHi : ℝ)
    (by norm_num [rightLo, rightHi]) q (poses source) (poseRadius source)
    (pose_radius_checked source) ha hb hd hs neighbors
  push_cast
  apply lt_of_not_ge
  intro lower
  apply excluded
  constructor
  · exact lower
  · norm_num [rightHi] at ⊢
    linarith only [bounds.2, radius]

noncomputable def lowerCut (source : Fin poseCount) : Row :=
  lower (leftHi + (poseRadius source).radius) true

noncomputable def upperCut (source : Fin poseCount) : Row :=
  upper (rightLo - (poseRadius source).radius) true

noncomputable def cutRows (source : Fin poseCount) : List Row :=
  lowerCut source :: upperCut source :: (poseRows source).map rows

theorem cutRows_hold (source : Fin poseCount) (q : OpenSquare)
    (hs : (poses source).OrientedRealizes q)
    (lo : ((leftHi + (poseRadius source).radius : ℚ) : ℝ) < centerX q)
    (hi : centerX q < ((rightLo - (poseRadius source).radius : ℚ) : ℝ)) :
    ∀ row ∈ cutRows source, row.Holds ![centerX q, centerY q] := by
  intro row hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact (holds_lower _ true _).mpr lo
  · rcases List.mem_cons.mp hr with rfl | hr
    · exact (holds_upper _ true _).mpr hi
    · obtain ⟨r, in_rows, rfl⟩ := List.mem_map.mp hr
      exact pose_row_holds hs r in_rows

#print axioms left_window
#print axioms right_window
end N12Compact.C898Chord.Fused
