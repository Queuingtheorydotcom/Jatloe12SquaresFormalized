import Compact.Geometry.ClosedPointExclusion
import Compact.Geometry.LongSection
import Compact.Geometry.ThreeSquareSupport

/-! A height boundary obtained directly from occupied row points.

The three foreign points may be on their owners' boundaries. An upper
compulsory point puts the fourth square above the blocked section, uniformly
over all orientations. Case713 uses row=87/50, upper height=47/20 and
original neighbors1,6,10; no propagated enclosure is an input.
-/

namespace N12Compact.CentralBarHeight

open S12 S12Pilot FourSquareAnchors SectionCapacity LongSectionGeometry ThreeSquare

/-- Three distinct occupied positions prevent a fourth square from having
a horizontal section longer than one at the same height. -/
theorem blocked_section (q : OpenSquare) (neighbors : Fin 3 → OpenSquare)
    (h : ℝ) (box : InsideContainer q)
    (points : ∀ i, ClosedInside (neighbors i) ((i.val : ℝ)+1) h)
    (apart : ∀ i x y, ¬ (q.Inside x y ∧ (neighbors i).Inside x y)) :
    ¬ LongSection q h := by
  intro hsection
  obtain ⟨i, hi⟩ := section_hits q h box hsection
  exact ClosedPointExclusion.outside_of_closed q (neighbors i) _ _
    (apart i) (points i) hi

/-- An upper point at least 0.51 above a blocked row identifies the upper
side of the radius exclusion. The small normalization cap is retained. -/
theorem center_above_blocked (q : OpenSquare) (h x y : ℝ)
    (ha : 1 < q.side) (cap : q.side ≤ 1001/1000)
    (top : ClosedInside q x y) (gap : h+51/100 ≤ y)
    (short : ¬ LongSection q h) : h+sectionRadius q < centerY q := by
  have hc := abs_nonneg q.c
  have hs := abs_nonneg q.s
  have sum : |q.c| + |q.s| ≤ 3/2 := by
    nlinarith [q.unit_normal, sq_abs q.c, sq_abs q.s,
      sq_nonneg (|q.c| - |q.s|)]
  have product : |q.c| * |q.s| ≤ 1/2 := by
    nlinarith only [q.unit_normal, sq_abs q.c, sq_abs q.s,
      sq_nonneg (|q.c| - |q.s|)]
  have topBound := (abs_le.mp (closed_support q x y 0 1 top)).2
  simp only [supportRadius, zero_mul, one_mul, zero_add, neg_zero]
    at topBound
  have sideBound := mul_le_mul_of_nonneg_right cap (add_nonneg hc hs)
  have radius : sectionRadius q =
      (|q.c| + |q.s| - 2 * |q.c| * |q.s|) / 2 := by
    simp only [sectionRadius, abs_mul]
    ring
  have lower : h-sectionRadius q ≤ centerY q := by
    rw [radius]
    nlinarith only [topBound, sideBound, sum, product, gap]
  apply lt_of_not_ge
  intro upper
  apply short
  apply horizontal_long_section q h ha
  apply abs_le.mpr
  constructor <;> linarith only [lower, upper]

/-- Original point ownership, containment, and disjointness supply every
premise of the height conclusion. No local radius cut is assumed. -/
theorem from_three_occupied_points (q : OpenSquare)
    (neighbors : Fin 3 → OpenSquare) (h x y : ℝ)
    (ha : 1 < q.side) (cap : q.side ≤ 1001/1000)
    (box : InsideContainer q)
    (top : ClosedInside q x y) (gap : h+51/100 ≤ y)
    (points : ∀ i, ClosedInside (neighbors i) ((i.val : ℝ)+1) h)
    (apart : ∀ i x y, ¬ (q.Inside x y ∧ (neighbors i).Inside x y)) :
    h+sectionRadius q < centerY q := by
  exact center_above_blocked q h x y ha cap top gap
    (blocked_section q neighbors h box points apart)

#print axioms from_three_occupied_points
end N12Compact.CentralBarHeight
