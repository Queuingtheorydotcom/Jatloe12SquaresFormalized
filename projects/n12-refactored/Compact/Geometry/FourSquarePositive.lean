import Compact.Geometry.FourSquareBLBridge
import Compact.Geometry.FourSquareLongitudinal
import Compact.Geometry.FourSquareAAll

/-! A whole symbolic branch of the four-square template: nonnegative
canonical B, with no orientation restriction on A or R.
The only model is the original OpenSquare.
All face and support inequalities used by the scalar endgame are derived
here from actual containment, required/missing points, and disjoint interiors.
-/

namespace N12Compact.FourSquarePositive

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare
open C977ChainBridge FourSquareBCorner FourSquareBLBridge

/-- B's nonnegative canonical sector, including its axis endpoint.
The A forced-point bridge covers every A and R orientation. -/
theorem impossible (A B L R : OpenSquare)
    (ha : 1 < B.side) (sideCap : B.side ≤ 1001 / 1000)
    (sameA : A.side = B.side) (sameL : B.side = L.side) (sameR : B.side = R.side)
    (bc : 0 < B.c) (bs : 0 ≤ B.s) (bsc : B.s ≤ B.c)
    (lc : 0 < L.c) (lsc : |L.s| ≤ L.c)
    (boxB : InsideContainer B) (boxL : InsideContainer L) (boxR : InsideContainer R)
    (aP : ClosedInside A 2 (113 / 50))
    (aQ : ClosedInside A (113 / 50) 2)
    (aT : ClosedInside A (47 / 20) (47 / 20))
    (aF : ¬ A.Inside (33 / 20) (33 / 20))
    (aG : ¬ A.Inside (47 / 20) (33 / 20))
    (bBottom : ClosedInside B (33 / 20) (47 / 20))
    (bTop : ClosedInside B (8 / 5) 3)
    (bTopRight : ClosedInside B (87 / 50) 3)
    (bMissingLeft : ¬ B.Inside 1 (1543 / 500))
    (bMissingRight : ¬ B.Inside 2 (1543 / 500))
    (lLeft : ClosedInside L (457 / 500) 2)
    (lTop : ClosedInside L 1 (12 / 5))
    (lMissingLow : ¬ L.Inside (19 / 25) (187 / 100))
    (lMissingRight : ¬ L.Inside (33 / 20) (33 / 20))
    (rTop : ClosedInside R 3 (12 / 5))
    (rRight : ClosedInside R (1543 / 500) 2)
    (rMissingLow : ¬ R.Inside (81 / 25) (187 / 100))
    (ab : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y))
    (ar : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (bl : ∀ x y, ¬ (B.Inside x y ∧ L.Inside x y))
    (br : ∀ x y, ¬ (B.Inside x y ∧ R.Inside x y)) : False := by
  have haA : 1 < A.side := by simpa only [sameA] using ha
  have haL : 1 < L.side := by simpa only [sameL] using ha
  have haR : 1 < R.side := by simpa only [sameR] using ha
  have highA := FourSquareAAll.point A B R haA haR boxR
    aP aQ aT aF aG bBottom rTop rRight rMissingLow ab ar
  have rowA := FourSquareAForced.row_point A aP highA
  have ba : ∀ x y, ¬ (B.Inside x y ∧ A.Inside x y) := by
    intro x y hp
    exact ab x y ⟨hp.2, hp.1⟩
  have short := no_long_section A B L R boxB lTop rowA rTop bl ba br
  have high := center_above_radius B bc.le bs bsc ha sideCap bTop short
  obtain ⟨cornerU, cornerV⟩ := upper_corner B bc bs bsc ha sideCap
    bBottom bTop bTopRight bMissingLeft bMissingRight short
  have steep := (corner_steep B bc.le bs bsc ha high cornerU cornerV).2
  have rowMissing := ClosedPointExclusion.outside_of_closed B L _ _ bl lTop
  have targetMissing : ¬ B.Inside 2 (5 / 2) := fun hp => ab _ _ ⟨highA, hp⟩
  obtain ⟨bottomV, height, wide⟩ := forced_lower_V B bc bs bsc ha steep
    bBottom bTop bTopRight rowMissing targetMissing cornerV
  have axes := BLLongitudinal.two_directed_alternatives B L bc bs bsc lc lsc
    haL bBottom bTop lLeft lTop lMissingLow lMissingRight sameL bl
  have lowV := missing_below_V B L bc bs bsc lc lsc ha haL
    bBottom bTop lLeft lTop lMissingLow lMissingRight cornerU cornerV bl
  have dot := dot_nonneg B L bc.le bs bsc lc.le lsc
  rcases axes with baxis | laxis
  · have cap := right_axis_cap B L baxis
    have radius : supportRadius L B.c B.s = B.side / 2 *
        ((B.c * L.c + B.s * L.s) + |B.c * L.s - B.s * L.c|) := by
      have cross : -B.c * L.s + B.s * L.c = -(B.c * L.s - B.s * L.c) := by ring
      simp only [supportRadius, cross, abs_neg, abs_of_nonneg dot, sameL]
    rw [radius] at cap
    have axis : B.c * centerX L + B.s * centerY L + B.side / 2 *
        ((B.c * L.c + B.s * L.s) + |B.c * L.s - B.s * L.c|) + B.side ≤
        2 * B.c + (1543 / 500) * B.s := by linarith only [cap, cornerU]
    have wall : B.side * (L.c + |L.s|) / 2 ≤ centerX L := by
      simpa only [sameL] using left_wall L lc.le boxL
    have vcenter : -L.s * (19 / 25) + L.c * (187 / 100) ≤
        -L.s * centerX L + L.c * centerY L - B.side / 2 := by
      have hh := (center_coordinates L).2
      rw [← sameL] at hh
      linarith only [lowV, hh]
    exact FourSquareLongitudinal.b_axis_impossible
      B.side B.c B.s L.c L.s (centerX L) (centerY L)
      ha bc bs bsc lc lsc B.unit_normal L.unit_normal wall vcenter height axis
  · have walls := left_upper_bounds L lc boxL lLeft lowV
    have caps := right_minimum_bounds B L dot cornerU cornerV bottomV laxis
    exact FourSquareLongitudinal.l_axis_impossible
      B.side B.c B.s L.c L.s (L.loU + L.side)
      ha bc bs bsc lc lsc B.unit_normal L.unit_normal wide
      (by simpa only [sameL] using walls.1)
      (by simpa only [sameL] using walls.2)
      (by intro ht; have hh := caps.1 ht; nlinarith only [hh]) caps.2

end N12Compact.FourSquarePositive
