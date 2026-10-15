import Compact.Completion.OtherCases.EightPointObstruction

/-! The literal final northeast obstruction of the new
C1089-SIMPLIFIED-PROOF.md section 5. This is the rigid chart
(xi,eta)=(3-x,y-2), applied to the same original square throughout.
The actual-family entrance that supplies these points is a separate task.
The older ten-point statement is retained as a wrapper. No whole-case
exclusion or compiler acceptance is asserted here. -/
namespace N12Compact.Completion.OtherCases.C1089.LastOrdinaryObstruction
open S12 S12Pilot
set_option Elab.async false

/-- Every exclusion in the completed chapter remains an individual actual
absence. The lower point, corner and two top points need not have a common
foreign owner. -/
theorem eight_point_impossible (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (47/20))
    (ordinary : q.Inside 3 (113/50))
    (halfpoint : ¬ q.Inside (5/2) 2)
    (corner : ¬ q.Inside 3 3)
    (low : ¬ q.Inside (273/100) (49/25))
    (topFar : ¬ q.Inside (64/25) 3)
    (topNear : ¬ q.Inside (113/50) 3)
    (origin : ¬ q.Inside 3 2) : False := by
  let r := (pullX q).translated 1 2
  have chart (x y : ℝ) : r.Inside x y ↔ q.Inside (3-x) (2+y) := by
    dsimp only [r]
    rw [inside_translated_iff,inside_pullX]
    rw [show (4:ℝ)-(1+x)=3-x by ring]
  have data : EightPointObstruction.Input r where
    side := side
    marker := (chart _ _).mpr (by convert marker using 1 <;> norm_num)
    anchor := (chart _ _).mpr (by convert ordinary using 1 <;> norm_num)
    origin := fun own => origin (by
      have actual := (chart _ _).mp own
      convert actual using 1 <;> norm_num)
    middle := fun own => halfpoint (by
      have actual := (chart _ _).mp own
      convert actual using 1 <;> norm_num)
    corner := fun own => corner (by
      have actual := (chart _ _).mp own
      convert actual using 1 <;> norm_num)
    lower := fun own => low (by
      have actual := (chart _ _).mp own
      convert actual using 1 <;> norm_num)
    topNear := fun own => topFar (by
      have actual := (chart _ _).mp own
      convert actual using 1 <;> norm_num)
    topFar := fun own => topNear (by
      have actual := (chart _ _).mp own
      convert actual using 1 <;> norm_num)
  exact EightPointObstruction.impossible r data

/-- The previous local interface remains available to existing callers.
The new proof no longer needs its wall-marker or extra horizontal exclusion. -/
theorem impossible (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (47/20))
    (ordinary : q.Inside 3 (113/50))
    (wallMarker : ¬ q.Inside (1543/500) 2)
    (halfpoint : ¬ q.Inside (5/2) 2)
    (inner : ¬ q.Inside (113/50) 2)
    (corner : ¬ q.Inside 3 3)
    (low : ¬ q.Inside (273/100) (49/25))
    (topFar : ¬ q.Inside (64/25) 3)
    (topNear : ¬ q.Inside (113/50) 3)
    (origin : ¬ q.Inside 3 2) : False :=
  eight_point_impossible q side marker ordinary halfpoint corner low topFar topNear origin

#print axioms eight_point_impossible
#print axioms impossible
end N12Compact.Completion.OtherCases.C1089.LastOrdinaryObstruction
