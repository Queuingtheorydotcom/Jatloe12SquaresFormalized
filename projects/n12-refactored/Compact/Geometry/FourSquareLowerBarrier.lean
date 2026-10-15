import Compact.Geometry.WallLowerBarrier
import Compact.Geometry.FourSquareHighRight

/-! Variant of the shared template for eleven further original cases.
The missing lower point belongs to an actual foreign square. This module
proves the geometry; case adapters must still prove that ownership. -/
namespace N12Compact.FourSquareLowerBarrier

open S12 S12Pilot FourSquareAnchors

structure Premises (A B L R : OpenSquare) : Prop
    extends FourSquareHighRight.Premises A B L R where
  rRight : ClosedInside R (1543/500) 2
  rMissingRow : ¬ R.Inside 3 (87/50)

theorem right_point (q a : OpenSquare) (ha : 1 < q.side)
    (box : InsideContainer q)
    (hP : ClosedInside q (1543/500) 2)
    (hQ : ClosedInside q 3 (12/5))
    (hW : ¬ q.Inside 3 (87/50))
    (hA : ClosedInside a (113/50) 2)
    (apart : ∀ x y, ¬ (q.Inside x y ∧ a.Inside x y)) :
    q.Inside 3 (5/2) := by
  have hD := ClosedPointExclusion.outside_of_closed q a (113/50) 2 apart hA
  obtain ⟨r, hc, hs, hside, hi, hcl⟩ := ClosedFrames.positive_frame (pullX q)
  have hri (x y : ℝ) : r.Inside x y ↔ q.Inside (4-x) y :=
    (hi x y).trans (inside_pullX q x y)
  have hrcl (x y : ℝ) : ClosedInside r x y ↔ ClosedInside q (4-x) y :=
    (hcl x y).trans (ClosedFrames.closed_pullX q x y)
  have hwall : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y hp
    have hb := box (4-x) y ((hri x y).mp hp)
    exact ⟨by linarith [hb.2.1], hb.2.2.1⟩
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
  have hrW : ¬ r.Inside 1 (87/50) := by
    intro hp
    apply hW
    have hh := (hri _ _).mp hp
    norm_num at hh
    exact hh
  have hrD : ¬ r.Inside (87/50) 2 := by
    intro hp
    apply hD
    have hh := (hri _ _).mp hp
    norm_num at hh
    exact hh
  have point := WallLowerBarrier.left_positive_point r
    (by simpa only [hside, pullX] using ha) hc hs hvertex hrP hrQ hrW hrD
  have hq := (hri _ _).mp point
  norm_num at hq
  exact hq

theorem impossible (A B L R : OpenSquare) (h : Premises A B L R) : False := by
  have hr : 1 < R.side := by simpa only [h.sameR] using h.one_lt
  have high := right_point R A hr h.boxR h.rRight h.rTop h.rMissingRow h.aQ
    (fun x y hp => h.ar x y ⟨hp.2, hp.1⟩)
  exact FourSquareHighRight.impossible A B L R h.toPremises high

#print axioms impossible
end N12Compact.FourSquareLowerBarrier
