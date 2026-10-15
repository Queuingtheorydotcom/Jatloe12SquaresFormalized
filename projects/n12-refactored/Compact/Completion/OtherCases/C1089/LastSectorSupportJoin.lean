import Compact.Completion.OtherCases.C1089.LastOrdinaryObstruction
import Compact.Completion.OtherCases.SouthwestSupportPoint.Main

/-! C1089-LAST-SECTOR-ENDING.md sections 3--5, after its section 2 has
forced the actual southwest G3. The southeast support point is derived,
not assumed. Both of its foreign segments retain their named actual
owners. The resulting point supplies the final ordinary-origin obstruction.
The finite original entrance and section 2 are separate source obligations.
This source has not been compiled. -/
namespace N12Compact.Completion.OtherCases.C1089.LastSectorSupportJoin
open S12 S12Pilot
set_option Elab.async false

structure BaseData (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i, 1 < (q i).side
  apart : ∀ i j, i ≠ j → ∀ x y, ¬((q i).Inside x y ∧ (q j).Inside x y)
  southwestMarker : (q 4).Inside (33/20) (33/20)
  southeastMarker : (q 5).Inside (47/20) (33/20)
  southeastF4 : (q 5).Inside 2 (87/50)
  southeastG6 : (q 5).Inside (113/50) 2
  southeastEast : (q 5).Inside (5/2) 2
  southeastSouth : (q 5).Inside 2 (3/2)
  northeastMarker : (q 6).Inside (47/20) (47/20)
  northeastF9 : (q 6).Inside 3 (113/50)
  rightLow : (q 10).Inside 3 (36/25)
  rightOrigin : (q 10).Inside 3 2
  bottomOrigin : (q 9).Inside 2 1
  bottomNear : (q 9).Inside (113/50) 1
  bottomAdvance : (q 9).Inside (14/5) 1
  topOrigin : (q 11).Inside 2 3
  topAdvance : (q 11).Inside (64/25) 3
  northeastCorner : (q 2).Inside 3 3

/-- The support-point join needs the southwest extra point. The preceding
actual point table is separated so that this point can be proved upstream. -/
structure Data (q : Fin 12 → OpenSquare) : Prop extends BaseData q where
  southwestExtra : (q 4).Inside (87/50) 2

/-- The literal reflection of the southwest support-point theorem.
No hypothetical replacement square or common owner for the bars is used. -/
theorem southeast_point (q : Fin 12 → OpenSquare) (h : Data q) :
    (q 5).Inside (273/100) (49/25) := by
  have bottomMiddle : (q 9).Inside (5/2) 1 := by
    convert inside_segment (q 9) (113/50) 1 (14/5) 1 (4/9)
      h.bottomNear h.bottomAdvance (by norm_num) (by norm_num) using 1 <;> norm_num
  have rightBar := WallProfile.vertical_owned (q 10) 3 (36/25) 2 (by norm_num)
    h.rightLow h.rightOrigin
  have rightFirst : (q 10).Inside 3 (8/5) := rightBar _ (by norm_num) (by norm_num)
  have rightLast : (q 10).Inside 3 (87/50) := rightBar _ (by norm_num) (by norm_num)
  have result := SouthwestSupportPoint.point_of_neighbours
    (pullX (q 5)) (pullX (q 9)) (pullX (q 4)) (h.side 5)
    (by norm_num [inside_pullX]; exact h.southeastMarker)
    (by norm_num [inside_pullX]; exact h.southeastF4)
    (by norm_num [inside_pullX]; exact h.southeastG6)
    (by norm_num [inside_pullX]; exact h.southeastEast)
    (by norm_num [inside_pullX]; exact h.southeastSouth)
    (by
      intro own
      have actual := (inside_pullX _ _ _).mp own
      norm_num at actual
      exact h.apart 5 6 (by decide) _ _ ⟨actual,h.northeastMarker⟩)
    (by
      intro own
      have actual := (inside_pullX _ _ _).mp own
      norm_num at actual
      exact h.apart 5 9 (by decide) _ _ ⟨actual,h.bottomOrigin⟩)
    (by
      intro own
      have actual := (inside_pullX _ _ _).mp own
      norm_num at actual
      exact h.apart 5 10 (by decide) _ _ ⟨actual,rightFirst⟩)
    (by
      intro own
      have actual := (inside_pullX _ _ _).mp own
      norm_num at actual
      exact h.apart 5 10 (by decide) _ _ ⟨actual,rightLast⟩)
    (by norm_num [inside_pullX]; exact bottomMiddle)
    (by norm_num [inside_pullX]; exact h.bottomNear)
    (by norm_num [inside_pullX]; exact h.southwestMarker)
    (by norm_num [inside_pullX]; exact h.southwestExtra)
    (by
      intro x y pair
      exact h.apart 5 9 (by decide) _ _
        ⟨(inside_pullX _ _ _).mp pair.1,(inside_pullX _ _ _).mp pair.2⟩)
    (by
      intro x y pair
      exact h.apart 5 4 (by decide) _ _
        ⟨(inside_pullX _ _ _).mp pair.1,(inside_pullX _ _ _).mp pair.2⟩)
  norm_num [inside_pullX] at result
  exact result

/-- The full last support join from the chapter's established actual
point table and the previously forced southwest extra auxiliary. -/
theorem impossible (q : Fin 12 → OpenSquare) (h : Data q) : False := by
  have low := southeast_point q h
  have topInner : (q 11).Inside (113/50) 3 := by
    convert inside_segment (q 11) 2 3 (64/25) 3 (13/28)
      h.topOrigin h.topAdvance (by norm_num) (by norm_num) using 1 <;> norm_num
  exact LastOrdinaryObstruction.eight_point_impossible (q 6) (h.side 6)
    h.northeastMarker h.northeastF9
    (fun own => h.apart 6 5 (by decide) _ _ ⟨own,h.southeastEast⟩)
    (fun own => h.apart 6 2 (by decide) _ _ ⟨own,h.northeastCorner⟩)
    (fun own => h.apart 6 5 (by decide) _ _ ⟨own,low⟩)
    (fun own => h.apart 6 11 (by decide) _ _ ⟨own,h.topAdvance⟩)
    (fun own => h.apart 6 11 (by decide) _ _ ⟨own,topInner⟩)
    (fun own => h.apart 6 10 (by decide) _ _ ⟨own,h.rightOrigin⟩)

#print axioms southeast_point
#print axioms impossible
end N12Compact.Completion.OtherCases.C1089.LastSectorSupportJoin
