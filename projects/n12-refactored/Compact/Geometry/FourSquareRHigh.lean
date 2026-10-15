import Compact.Geometry.ClosedFrames
import Compact.Geometry.ClosedPointExclusion
import Compact.Geometry.WallForcedPoint

/-! The right square is forced through (3,5/2). This uses its original wall,
two closed owned points, one missing point, and disjointness from A's closed
point. All orientations and closed ownership ties are retained. -/

namespace N12Compact.FourSquareRHigh

open S12 S12Pilot FourSquareAnchors

theorem right_point (q a : OpenSquare) (ha : 1 < q.side)
    (box : ∀ x y, q.Inside x y → 0 ≤ x ∧ x ≤ 4 ∧ 0 ≤ y ∧ y ≤ 4)
    (hP : ClosedInside q (1543/500) 2)
    (hQ : ClosedInside q 3 (12/5))
    (hW : ¬ q.Inside (81/25) (187/100))
    (hA : ClosedInside a (113/50) 2)
    (apart : ∀ x y, ¬ (q.Inside x y ∧ a.Inside x y)) :
    q.Inside 3 (5/2) := by
  have hD := ClosedPointExclusion.outside_of_closed q a (113/50) 2 apart hA
  obtain ⟨r,hc,hs,hside,hi,hcl⟩ := ClosedFrames.positive_frame (pullX q)
  have hri (x y : ℝ) : r.Inside x y ↔ q.Inside (4-x) y :=
    (hi x y).trans (inside_pullX q x y)
  have hrcl (x y : ℝ) : ClosedInside r x y ↔ ClosedInside q (4-x) y :=
    (hcl x y).trans (ClosedFrames.closed_pullX q x y)
  have hwall : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y hr
    have hb := box (4-x) y ((hri x y).mp hr)
    exact ⟨by linarith [hb.2.1],hb.2.2.1⟩
  have hvertex : 0 ≤ r.c*r.loU-r.s*(r.loV+r.side) := by
    have hx := (positive_frame_wall_bounds r hc.le hs hwall).1
    dsimp [centerX] at hx
    nlinarith only [hx]
  have hrP : ClosedInside r (457/500) 2 := by
    apply (hrcl _ _).mpr
    norm_num
    exact hP
  have hrQ : ClosedInside r 1 (12/5) := by
    apply (hrcl _ _).mpr
    norm_num
    exact hQ
  have hrW : ¬ r.Inside (19/25) (187/100) := by
    intro h
    apply hW
    have hh := (hri _ _).mp h
    norm_num at hh
    exact hh
  have hrD : ¬ r.Inside (87/50) 2 := by
    intro h
    apply hD
    have hh := (hri _ _).mp h
    norm_num at hh
    exact hh
  have point := WallForcedPoint.left_positive_point r (by simpa only [hside, pullX] using ha)
    hc hs hvertex hrP hrQ hrW hrD
  have hq := (hri _ _).mp point
  norm_num at hq
  exact hq

#print axioms right_point
end N12Compact.FourSquareRHigh
